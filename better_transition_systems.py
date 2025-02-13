from collections.abc import MutableSet, Iterator, Iterable
from dataclasses import dataclass
from typing import Literal, Self

import z3

class ImmutableFun(z3.FuncDeclRef):
    signature: tuple[z3.SortRef, ...]

    def __init__(self, name: str, *signature: z3.SortRef) -> None:
        fun = z3.Function(name, *signature)
        super(ImmutableFun, self).__init__(fun.ast, fun.ctx)
        self.signature = signature

    @staticmethod
    def mutable() -> Literal[False]:
        return False


class MutableFun(ImmutableFun):
    @property
    def next(self) -> Self:
        return self.__class__(self.name() + "'", *self.signature)

    @staticmethod
    def mutable() -> Literal[True]:
        return True


class ImmutableRelation(z3.FuncDeclRef):
    signature: tuple[z3.SortRef, ...]

    def __init__(self, name: str, *signature: z3.SortRef) -> None:
        fun = z3.Function(name, *signature, z3.BoolSort())
        super(ImmutableRelation, self).__init__(fun.ast, fun.ctx)
        self.signature = signature

    def __call__(self, *args: z3.ExprRef) -> z3.BoolRef:
        return super().__call__(*args)

    @staticmethod
    def mutable() -> Literal[False]:
        return False


class MutableRelation(ImmutableRelation):
    @property
    def next(self) -> Self:
        return self.__class__(self.name() + "'", *self.signature)

    @staticmethod
    def mutable() -> Literal[True]:
        return True


class ImmutableConst(z3.ExprRef):
    const_name: str
    signature: z3.SortRef

    def __init__(self, name: str, signature: z3.SortRef) -> None:
        const = z3.Const(name, signature)
        super(ImmutableConst, self).__init__(const.ast, const.ctx)
        self.const_name = name
        self.signature = signature
    @staticmethod
    def mutable() -> Literal[False]:
        return False


class MutableConst(ImmutableConst):
    @property
    def next(self) -> Self:
        return self.__class__(self.const_name + "'", self.signature)

    @staticmethod
    def mutable() -> Literal[True]:
        return True

type Symbol = ImmutableConst | ImmutableRelation | ImmutableFun
type MutableSymbol = MutableConst | MutableRelation | MutableFun

@dataclass(frozen=True)
class SymbolWrapper[T: Symbol]:
    symbol: T

    def __eq__(self, other: object) -> bool:
        return isinstance(other, SymbolWrapper) and self.symbol.eq(other.symbol)

    def __hash__(self) -> int:
        return hash(self.symbol)


@dataclass
class SymbolSet[T: Symbol](MutableSet[T]):
    data: set[SymbolWrapper[T]]

    @classmethod
    def from_iterable(cls, iterable: Iterable[T]) -> Self:
        return cls({SymbolWrapper(symbol) for symbol in iterable})

    @classmethod
    def from_args(cls, *args: T) -> Self:
        return cls.from_iterable(args)

    def add(self, value: T) -> None:
        self.data.add(SymbolWrapper(value))

    def discard(self, value: T) -> None:
        self.data.discard(SymbolWrapper(value))

    def __contains__(self, value: T) -> bool:
        return SymbolWrapper(value) in self.data

    def __len__(self) -> int:
        return len(self.data)

    def __iter__(self) -> Iterator[T]:
        return iter(wrapper.symbol for wrapper in self.data)


## Tests

f = MutableFun("f", z3.IntSort(), z3.IntSort())
x = MutableConst("x", z3.IntSort())
p = MutableRelation("p", z3.IntSort())


formula = f(x) != f(x)
solver = z3.Solver()
assert solver.check(formula) == z3.unsat
formula2 = f(x) != f.next(x)
assert solver.check(formula2) == z3.sat
print(solver.model())
formula3 = z3.And(x == f(x), p(x), z3.Not(p(f(x))))
assert solver.check(formula3) == z3.unsat
formula4 = z3.And(x == f(x), p(x), z3.Not(p.next(f.next(x))))
assert solver.check(formula4) == z3.sat
print(solver.model())
formula5 = f(x) != f(x.next)
assert solver.check(formula5) == z3.sat
print(solver.model())

print("ok")