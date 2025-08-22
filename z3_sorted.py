from functools import cached_property
from typing import cast, Self, TYPE_CHECKING

import z3

if TYPE_CHECKING:

    class SortedExpr(z3.Const):
        @classmethod
        def ref(cls) -> z3.SortRef: ...

        @classmethod
        def const(cls, name: str) -> Self: ...

        @classmethod
        def consts(cls, names: str) -> list[Self]: ...

else:

    class SortedExpr(z3.ExprRef):
        @classmethod
        def ref(cls) -> z3.SortRef:
            return z3.DeclareSort(cls.__name__)

        @classmethod
        def const(cls, name: str) -> Self:
            return z3.Const(name, cls.ref())

        @classmethod
        def consts(cls, names: str) -> tuple[Self, ...]:
            return z3.Consts(names, cls.ref())


type Sort = type[SortedExpr]


class Bool(SortedExpr):
    @classmethod
    def ref(cls) -> z3.SortRef:
        return z3.BoolSort()


class Fun(z3.FuncDeclRef):
    fun_name: str
    signature: tuple[Sort, ...]
    mutable: bool

    def __init__(
        self, name: str, *signature: Sort, mutable: bool = True
    ) -> None:
        ref_signature = tuple(sort.ref() for sort in signature)
        fun = z3.Function(name, *ref_signature)
        super(Fun, self).__init__(fun.ast, fun.ctx)
        self.fun_name = name
        self.signature = signature
        self.mutable = mutable

    @cached_property
    def next(self) -> Self:
        if self.mutable:
            return self.__class__(
                self.fun_name + "'", *self.signature, mutable=self.mutable
            )
        return self

    @cached_property
    def sorts(self) -> set[z3.SortRef]:
        return {sort.ref() for sort in self.signature}


class Rel(Fun):
    def __init__(
        self, name: str, *signature: Sort, mutable: bool = True
    ) -> None:
        super().__init__(name, *signature, Bool, mutable=mutable)

    def __call__(self, *args: z3.ExprRef) -> z3.BoolRef:
        return cast(z3.BoolRef, super().__call__(*args))


class Const(z3.ExprRef):
    const_name: str
    const_sort: Sort
    mutable: bool

    def __init__(self, name: str, sort: Sort, mutable: bool = True) -> None:
        const = z3.Const(name, sort.ref())
        super(Const, self).__init__(const.ast, const.ctx)
        self.const_name = name
        self.const_sort = sort
        self.mutable = mutable

    @cached_property
    def next(self) -> Self:
        return self.__class__(
            self.const_name + "'", self.const_sort, mutable=self.mutable
        )

    @cached_property
    def fun(self) -> Fun:
        return Fun(self.const_name, self.const_sort, mutable=self.mutable)
