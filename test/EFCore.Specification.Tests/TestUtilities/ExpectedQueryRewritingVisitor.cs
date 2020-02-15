// Copyright (c) .NET Foundation. All rights reserved.
// Licensed under the Apache License, Version 2.0. See License.txt in the project root for license information.

using System;
using System.Linq;
using System.Linq.Expressions;
using System.Reflection;
using Microsoft.EntityFrameworkCore.Query;

namespace Microsoft.EntityFrameworkCore.TestUtilities
{
    public class ExpectedQueryRewritingVisitor : ExpressionVisitor
    {
        private static readonly MethodInfo _maybeMethod = typeof(QueryTestExtensions).GetMethod(nameof(QueryTestExtensions.Maybe));
        private readonly MethodInfo _maybeScalarNullableMethod;
        private readonly MethodInfo _maybeScalarNonNullableMethod;

        private bool _negated = false;

        public ExpectedQueryRewritingVisitor()
        {
            var maybeScalarMethods = typeof(QueryTestExtensions).GetMethods()
                .Where(m => m.Name == nameof(QueryTestExtensions.MaybeScalar))
                .Select(m => new
                {
                    method = m,
                    argument = m.GetParameters()[1].ParameterType.GetGenericArguments()[1]
                });

            _maybeScalarNullableMethod = maybeScalarMethods.Single(x => x.argument.IsNullableValueType()).method;
            _maybeScalarNonNullableMethod = maybeScalarMethods.Single(x => !x.argument.IsNullableValueType()).method;
        }

        protected override Expression VisitMember(MemberExpression memberExpression)
        {
            if (!memberExpression.Type.IsValueType
                && !memberExpression.Type.IsNullableValueType()
                && memberExpression.Expression != null)
            { 
                var expression = Visit(memberExpression.Expression);

                var lambdaParameter = Expression.Parameter(expression.Type, "x");
                var lambda = Expression.Lambda(memberExpression.Update(lambdaParameter), lambdaParameter);
                var method = _maybeMethod.MakeGenericMethod(expression.Type, memberExpression.Type);

                return Expression.Call(method, expression, lambda);
            }

            return base.VisitMember(memberExpression);
        }

        protected override Expression VisitMethodCall(MethodCallExpression methodCallExpression)
        {
            if (methodCallExpression.Method.DeclaringType == typeof(Queryable)
                && methodCallExpression.Method.IsGenericMethod
                && (methodCallExpression.Method.GetGenericMethodDefinition() == QueryableMethods.Join
                    || methodCallExpression.Method.GetGenericMethodDefinition() == QueryableMethods.GroupJoin))
            {
                var outer = Visit(methodCallExpression.Arguments[0]);
                var inner = Visit(methodCallExpression.Arguments[1]);
                var resultSelector = Visit(methodCallExpression.Arguments[4]);

                var originalLeftKeySelectorLambda = methodCallExpression.Arguments[2].UnwrapLambdaFromQuote();
                var originalRightKeySelectorLambda = methodCallExpression.Arguments[3].UnwrapLambdaFromQuote();
                var leftKeySelectorBody = AddNullProtectionForNonNullableMemberAccess(originalLeftKeySelectorLambda.Body);
                var rightKeySelectorBody = AddNullProtectionForNonNullableMemberAccess(originalRightKeySelectorLambda.Body);

                if (leftKeySelectorBody.Type.IsNullableValueType()
                    && rightKeySelectorBody.Type.IsValueType
                    && leftKeySelectorBody.Type.UnwrapNullableType() == rightKeySelectorBody.Type)
                {
                    rightKeySelectorBody = Expression.Convert(rightKeySelectorBody, leftKeySelectorBody.Type);
                }

                if (rightKeySelectorBody.Type.IsNullableValueType()
                    && leftKeySelectorBody.Type.IsValueType
                    && rightKeySelectorBody.Type.UnwrapNullableType() == leftKeySelectorBody.Type)
                {
                    leftKeySelectorBody = Expression.Convert(leftKeySelectorBody, rightKeySelectorBody.Type);
                }

                var keySelectorTypeChanged = false;
                var joinMethodInfo = methodCallExpression.Method;
                var joinMethodInfoGenericArguments = methodCallExpression.Method.GetGenericArguments();

                if ((leftKeySelectorBody.Type != methodCallExpression.Arguments[2].UnwrapLambdaFromQuote().Body.Type)
                    || (rightKeySelectorBody.Type != methodCallExpression.Arguments[3].UnwrapLambdaFromQuote().Body.Type))
                {
                    joinMethodInfoGenericArguments[2] = leftKeySelectorBody.Type;
                    joinMethodInfo = joinMethodInfo.GetGenericMethodDefinition().MakeGenericMethod(joinMethodInfoGenericArguments);
                    keySelectorTypeChanged = true;
                }

                var leftKeySelector = keySelectorTypeChanged
                    ? Expression.Lambda(
                        leftKeySelectorBody,
                        methodCallExpression.Arguments[2].UnwrapLambdaFromQuote().Parameters)
                    : Expression.Lambda(
                        originalLeftKeySelectorLambda.Type,
                        leftKeySelectorBody,
                        methodCallExpression.Arguments[2].UnwrapLambdaFromQuote().Parameters);

                var rightKeySelector = keySelectorTypeChanged
                    ? Expression.Lambda(
                        rightKeySelectorBody,
                        methodCallExpression.Arguments[3].UnwrapLambdaFromQuote().Parameters)
                    : Expression.Lambda(
                        originalRightKeySelectorLambda.Type,
                        rightKeySelectorBody,
                        methodCallExpression.Arguments[3].UnwrapLambdaFromQuote().Parameters);

                return Expression.Call(
                    joinMethodInfo,
                    outer,
                    inner,
                    leftKeySelector,
                    rightKeySelector,
                    resultSelector);
            }

            if (Infrastructure.MethodInfoExtensions.IsEFPropertyMethod(methodCallExpression.Method))
            {
                var rewritten = TryConvertEFPropertyToMemberAccess(methodCallExpression);

                return Visit(rewritten);
            }

            return base.VisitMethodCall(methodCallExpression);
        }

        private Expression TryConvertEFPropertyToMemberAccess(Expression expression)
        {
            return expression is MethodCallExpression methodCallExpression
                && Infrastructure.MethodInfoExtensions.IsEFPropertyMethod(methodCallExpression.Method)
                ? Expression.Property(
                    RemoveConvert(methodCallExpression.Arguments[0]),
                    Expression.Lambda<Func<string>>(methodCallExpression.Arguments[1]).Compile().Invoke())
                : expression;

            static Expression RemoveConvert(Expression expression)
                => expression is UnaryExpression unaryExpression
                    && (expression.NodeType == ExpressionType.Convert
                        || expression.NodeType == ExpressionType.ConvertChecked)
                    ? RemoveConvert(unaryExpression.Operand)
                    : expression;
        }

        private Expression AddNullProtectionForNonNullableMemberAccess(Expression expression)
        {
            expression = TryConvertEFPropertyToMemberAccess(expression);

            if (expression is MemberExpression memberExpression
                && (memberExpression.Type.IsValueType || memberExpression.Type.IsNullableValueType())
                && memberExpression.Expression != null)
            {
                var instance = Visit(memberExpression.Expression);
                var maybeLambdaParameter = Expression.Parameter(instance.Type, "x");
                var maybeLambda = Expression.Lambda(memberExpression.Update(maybeLambdaParameter), maybeLambdaParameter);

                var methodInfo = (memberExpression.Type.IsNullableValueType()
                    ? _maybeScalarNullableMethod
                    : _maybeScalarNonNullableMethod).MakeGenericMethod(
                        instance.Type,
                        memberExpression.Type.UnwrapNullableType());

                return Expression.Call(methodInfo, instance, maybeLambda);
            }

            return Visit(expression);
        }

        protected override Expression VisitUnary(UnaryExpression unaryExpression)
        {
            if ((unaryExpression.NodeType == ExpressionType.Convert || unaryExpression.NodeType == ExpressionType.ConvertChecked || unaryExpression.NodeType == ExpressionType.TypeAs)
                && unaryExpression.Operand is MemberExpression memberOperand
                && memberOperand.Type.IsValueType
                && !memberOperand.Type.IsNullableValueType()
                && memberOperand.Expression != null
                && unaryExpression.Type.IsNullableValueType()
                && unaryExpression.Type.UnwrapNullableType() == memberOperand.Type)
            {
                var expression = Visit(memberOperand.Expression);

                var lambdaParameter = Expression.Parameter(expression.Type, "x");
                var lambda = Expression.Lambda(memberOperand.Update(lambdaParameter), lambdaParameter);
                var method = _maybeScalarNonNullableMethod.MakeGenericMethod(expression.Type, memberOperand.Type);

                return unaryExpression.Update(
                    Expression.Call(method, expression, lambda));
            }

            if (unaryExpression.NodeType == ExpressionType.Not)
            {
                var negated = _negated;
                _negated = true;
                var operand = Visit(unaryExpression.Operand);
                _negated = negated;

                return unaryExpression.Update(operand);
            }

            return base.VisitUnary(unaryExpression);
        }

        protected override Expression VisitBinary(BinaryExpression binaryExpression)
        {
            if (binaryExpression.NodeType == ExpressionType.Equal
                || binaryExpression.NodeType == ExpressionType.NotEqual
                || binaryExpression.NodeType == ExpressionType.GreaterThan
                || binaryExpression.NodeType == ExpressionType.GreaterThanOrEqual
                || binaryExpression.NodeType == ExpressionType.LessThan
                || binaryExpression.NodeType == ExpressionType.LessThanOrEqual)
            {
                var left = AddNullProtectionForNonNullableMemberAccess(binaryExpression.Left);
                var right = AddNullProtectionForNonNullableMemberAccess(binaryExpression.Right);

                if (left.Type.IsNullableValueType()
                    && right.Type.IsValueType
                    && left.Type.UnwrapNullableType() == right.Type)
                {
                    right = Expression.Convert(right, left.Type);
                }

                if (right.Type.IsNullableValueType()
                    && left.Type.IsValueType
                    && right.Type.UnwrapNullableType() == left.Type)
                {
                    left = Expression.Convert(left, right.Type);
                }

                return binaryExpression.Update(left, binaryExpression.Conversion, right);
            }

            return base.VisitBinary(binaryExpression);
        }
    }
}
