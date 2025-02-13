from typing import overload

import z3

from rewriter._internals import clone as internal_clone
from rewriter._internals import rewrite as internal_rewrite


def clone_vars(quantifier: z3.QuantifierRef) -> list[z3.Const]:
    return [
        z3.Const(quantifier.var_name(i), quantifier.var_sort(i))
        for i in range(quantifier.num_vars())
    ]


def clone_quantifier(
    quantifier: z3.QuantifierRef, body: z3.BoolRef
) -> z3.QuantifierRef:
    bound_vars = clone_vars(quantifier)

    if quantifier.is_forall():
        return z3.ForAll(bound_vars, body)
    else:
        return z3.Exists(bound_vars, body)


def clone[
    AnyExprRef: z3.ExprRef
](expression: AnyExprRef, *args: z3.ExprRef) -> AnyExprRef:
    return internal_clone(expression, *args)


def rewrite[
    AnyExprRef: z3.ExprRef
](expression: AnyExprRef, fun: z3.FuncDeclRef, term: z3.ExprRef) -> AnyExprRef:
    return internal_rewrite(expression, fun, term)
