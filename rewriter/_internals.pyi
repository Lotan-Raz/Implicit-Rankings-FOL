from typing import TypeVar

import z3

T = TypeVar("T", bound=z3.ExprRef)

def clone(expression: T, *args: z3.ExprRef) -> T: ...
def rewrite(expression: T, fun: z3.FuncDeclRef, term: z3.ExprRef) -> T: ...
