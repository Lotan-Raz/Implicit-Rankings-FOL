# type: ignore

from z3 import (
    Z3_APP_AST,
    Z3_ARRAY_SORT,
    Z3_BOOL_SORT,
    Z3_BV_SORT,
    Z3_DATATYPE_SORT,
    Z3_FINITE_DOMAIN_SORT,
    Z3_FLOATING_POINT_SORT,
    Z3_INT_SORT,
    Z3_NUMERAL_AST,
    Z3_QUANTIFIER_AST,
    Z3_RE_SORT,
    Z3_REAL_SORT,
    Z3_ROUNDING_MODE_SORT,
    Z3_SEQ_SORT,
    AlgebraicNumRef,
    ArithRef,
    ArrayRef,
    Ast,
    AstMap,
    BitVecNumRef,
    BitVecRef,
    BoolRef,
    DatatypeRef,
    ExprRef,
    FiniteDomainNumRef,
    FiniteDomainRef,
    FPNumRef,
    FPRef,
    FPRMRef,
    IntNumRef,
    Pattern,
    PatternRef,
    QuantifierRef,
    RatNumRef,
    ReRef,
    SeqRef,
    Z3_get_ast_kind,
    Z3_get_sort,
    Z3_get_sort_kind,
    Z3_is_algebraic_number,
    Z3_is_numeral_ast,
    Z3_update_term,
    eq,
    is_app,
    is_quantifier,
    is_var,
    substitute_vars,
)


def _is_numeral(ctx, a):
    return Z3_is_numeral_ast(ctx.ref(), a)


def _is_algebraic(ctx, a):
    return Z3_is_algebraic_number(ctx.ref(), a)


def _to_expr_ref(a, ctx):
    if isinstance(a, Pattern):
        return PatternRef(a, ctx)
    ctx_ref = ctx.ref()
    k = Z3_get_ast_kind(ctx_ref, a)
    if k == Z3_QUANTIFIER_AST:
        return QuantifierRef(a, ctx)
    sk = Z3_get_sort_kind(ctx_ref, Z3_get_sort(ctx_ref, a))
    if sk == Z3_BOOL_SORT:
        return BoolRef(a, ctx)
    if sk == Z3_INT_SORT:
        if k == Z3_NUMERAL_AST:
            return IntNumRef(a, ctx)
        return ArithRef(a, ctx)
    if sk == Z3_REAL_SORT:
        if k == Z3_NUMERAL_AST:
            return RatNumRef(a, ctx)
        if _is_algebraic(ctx, a):
            return AlgebraicNumRef(a, ctx)
        return ArithRef(a, ctx)
    if sk == Z3_BV_SORT:
        if k == Z3_NUMERAL_AST:
            return BitVecNumRef(a, ctx)
        else:
            return BitVecRef(a, ctx)
    if sk == Z3_ARRAY_SORT:
        return ArrayRef(a, ctx)
    if sk == Z3_DATATYPE_SORT:
        return DatatypeRef(a, ctx)
    if sk == Z3_FLOATING_POINT_SORT:
        if k == Z3_APP_AST and _is_numeral(ctx, a):
            return FPNumRef(a, ctx)
        else:
            return FPRef(a, ctx)
    if sk == Z3_FINITE_DOMAIN_SORT:
        if k == Z3_NUMERAL_AST:
            return FiniteDomainNumRef(a, ctx)
        else:
            return FiniteDomainRef(a, ctx)
    if sk == Z3_ROUNDING_MODE_SORT:
        return FPRMRef(a, ctx)
    if sk == Z3_SEQ_SORT:
        return SeqRef(a, ctx)
    if sk == Z3_RE_SORT:
        return ReRef(a, ctx)
    return ExprRef(a, ctx)


def clone(expression, *args):
    n = len(args)
    _args = (Ast * n)()
    for i in range(n):
        _args[i] = args[i].as_ast()
    return _to_expr_ref(
        Z3_update_term(expression.ctx_ref(), expression.as_ast(), n, _args),
        expression.ctx,
    )


def rewrite(expression, fun, term):
    """
    Replace f-applications f(r_1, ..., r_n) with t[r_1, ..., r_n] in s.
    """
    todo = []  # to do list
    todo.append(expression)
    cache = AstMap(ctx=expression.ctx)
    while todo:
        n = todo[len(todo) - 1]
        if is_var(n):
            todo.pop()
            cache[n] = n
        elif is_app(n):
            visited = True
            new_args = []
            for i in range(n.num_args()):
                arg = n.arg(i)
                if not arg in cache:
                    todo.append(arg)
                    visited = False
                else:
                    new_args.append(cache[arg])
            if visited:
                todo.pop()
                g = n.decl()
                if eq(g, fun):
                    new_n = substitute_vars(term, *new_args)
                else:
                    new_n = clone(n, *new_args)
                cache[n] = new_n
        else:
            assert is_quantifier(n)
            b = n.body()
            if b in cache:
                todo.pop()
                new_n = clone(n, *[cache[b]])
                cache[n] = new_n
            else:
                todo.append(b)
    return cache[expression]
