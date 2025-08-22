import operator
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable
from functools import cached_property, reduce
from typing import get_type_hints, get_origin, Annotated, Self, cast, Protocol

import z3

from z3_helpers import sat_check, print_model_in_order
from z3_sorted import SortedExpr, Fun, Const, Sort

# todo: auto universal quant. for axiom and invariants?
type AxiomMethod = Callable[[], z3.BoolRef]
type TransitionMethod = Callable[..., z3.BoolRef]
type InvariantMethod = Callable[[], z3.BoolRef]

_TS_METADATA = "__ts_metadata__"
_TS_AXIOM = object()
_TS_TRANSITION = object()
_TS_INVARIANT = object()
_TS_SPECIALS = {"next", "axiom", "transition", "transitions", "invariant", "invariants"}


def axiom[**P, T](fun: Callable[P, T]) -> Callable[P, T]:
    setattr(fun, _TS_METADATA, _TS_AXIOM)
    return fun


def transition[**P, T](fun: Callable[P, T]) -> Callable[P, T]:
    setattr(fun, _TS_METADATA, _TS_TRANSITION)
    return fun


def invariant[**P, T](fun: Callable[P, T]) -> Callable[P, T]:
    setattr(fun, _TS_METADATA, _TS_INVARIANT)
    return fun


class TransitionSystem(ABC):
    suffix: str
    symbols: dict[str, Fun]

    def __init__(self, suffix: str = "") -> None:
        self.suffix = suffix
        self.symbols = {}
        for field, hint in get_type_hints(self.__class__, include_extras=True).items():
            if not get_origin(hint) is Annotated:
                continue
            signature: list[type[SortedExpr]] = [
                annotation
                for annotation in hint.__metadata__
                if isinstance(annotation, type) and issubclass(annotation, SortedExpr)
            ]
            mutable = not any(
                isinstance(annotation, str) and annotation == "immutable"
                for annotation in hint.__metadata__
            )
            origin = hint.__origin__
            symbol = origin(field + suffix, *signature, mutable=mutable)
            assert isinstance(symbol, Fun) or isinstance(symbol, Const)
            object.__setattr__(self, field, symbol)
            if isinstance(symbol, Const):
                self.symbols[field] = symbol.fun
            else:
                self.symbols[field] = symbol

    @cached_property
    def sorts(self) -> set[z3.SortRef]:
        return reduce(operator.or_, (fun.sorts for fun in self.symbols.values()))

    @cached_property
    def next(self) -> Self:
        return self.__class__(self.suffix + "'")

    def __getitem__(self, item: str) -> Fun:
        return self.symbols[item]

    def _get_methods[T](self, marker: object) -> Iterable[Callable[..., T]]:
        for name in dir(self):
            if name in _TS_SPECIALS:
                continue
            attr = getattr(self, name)
            if (
                callable(attr)
                and hasattr(attr, _TS_METADATA)
                and getattr(attr, _TS_METADATA) is marker
            ):
                yield attr

    @cached_property
    def axiom(self) -> z3.BoolRef:
        axioms: list[z3.BoolRef] = []
        method: AxiomMethod
        for method in self._get_methods(_TS_AXIOM):
            axioms.append(method())
        return z3.And(*axioms)

    @cached_property
    def invariants(self) -> dict[str, z3.BoolRef]:
        invariants: dict[str, z3.BoolRef] = {}
        method: InvariantMethod
        for method in self._get_methods(_TS_INVARIANT):
            invariants[method.__name__] = method()
        return invariants

    @cached_property
    def invariant(self) -> z3.BoolRef:
        return z3.And(*self.invariants.values())

    @cached_property
    def transitions(self) -> dict[str, z3.BoolRef]:
        transitions: dict[str, z3.BoolRef] = {}
        method: TransitionMethod
        for method in self._get_methods(_TS_TRANSITION):
            hints = get_type_hints(method, include_extras=True)
            args: list[z3.Const] = []
            for param, hint in hints.items():
                if param == "return":
                    continue

                assert isinstance(hint, type) and issubclass(hint, SortedExpr)
                args.append(z3.Const(param, hint.ref()))
            transitions[method.__name__] = z3.Exists(
                args, cast(z3.BoolRef, method(*args))
            )
        return transitions

    @cached_property
    def transition(self) -> z3.BoolRef:
        return z3.Or(*self.transitions.values())

    @abstractmethod
    def init(self) -> z3.BoolRef: ...

    def check_invariants(self) -> None:
        for inv_name, inv in self.invariants.items():
            print(f"Checking invariant {inv_name} in init: ", end="")
            self._check_and_print(self.axiom, self.init(), z3.Not(inv))

            for name, trans in self.transitions.items():
                print(f"Checking invariant {inv_name} in {name}: ", end="")
                self._check_and_print(
                    self.axiom,
                    self.next.axiom,
                    inv,
                    trans,
                    z3.Not(self.next.invariants[inv_name]),
                    with_next=True,
                )

    def _check_and_print(self, *args: z3.BoolRef, with_next: bool = False) -> None:
        symbols = list(self.symbols.values())
        if with_next:
            symbols += list(self.next.symbols.values())
        result = sat_check(args)
        if result[0] == z3.unsat:
            print("passed")
        else:
            print("failed")
            print_model_in_order(result, symbols, False)
