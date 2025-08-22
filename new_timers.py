import operator
from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass, field
from functools import cached_property, reduce
from typing import Any, cast

import z3

from better_ts import TransitionSystem
from z3_sorted import Rel, Bool

type ParamSpec = dict[str, z3.SortRef]
type Params = dict[str, z3.ExprRef]
type SymSpec = dict[str, tuple[z3.SortRef, ...]]
type Sym = dict[str, z3.FuncDeclRef]
type SymFormula = Callable[[Sym, Params], z3.BoolRef]

G = Rel("G", Bool, mutable=False)
F = Rel("F", Bool, mutable=False)


def timer_zero(timer_expr: z3.ExprRef) -> z3.BoolRef:
    # todo: configurable lia/uninterpreted
    return timer_expr == 0


def timer_nonzero(timer_expr: z3.ExprRef) -> z3.BoolRef:
    return timer_expr != 0


def timer_finite(timer_expr: z3.ExprRef) -> z3.BoolRef:
    # todo configurable
    return timer_expr >= 0  # type: ignore


def timer_infinite(timer_expr: z3.ExprRef) -> z3.BoolRef:
    # todo configurable
    return timer_expr == -1


@dataclass(frozen=True)
class Z3Wrapper[T: z3.ExprRef]:
    expr: T

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Z3Wrapper):
            return False

        return other.expr.eq(self.expr)

    def __hash__(self):
        return hash(self.expr)


@dataclass(frozen=True)
class TimerId:
    formula: z3.BoolRef

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Timer):
            return False
        return self.formula.eq(other.formula)

    def __hash__(self) -> int:
        return hash(self.formula)


@dataclass(frozen=True)
class Timer(ABC):
    formula: z3.BoolRef
    fun: str
    params: ParamSpec

    @cached_property
    def id(self) -> TimerId:
        return TimerId(self.formula)

    @cached_property
    def signature(self) -> tuple[z3.SortRef, ...]:
        return tuple(v for v in self.params.values())

    @cached_property
    def args(self) -> tuple[str, ...]:
        return tuple(self.params.keys())

    @cached_property
    def sym_spec(self) -> SymSpec:
        return {self.fun: self.signature}

    def term(self, sym: Sym, params: Params) -> z3.ExprRef:
        return sym[self.fun](*(params[arg] for arg in self.args))

    @abstractmethod
    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef: ...

    def transition(
        self, pre_sym: Sym, post_sym: Sym, params: Params
    ) -> None | z3.BoolRef:
        return None


@dataclass(frozen=True)
class AtomicTimer(Timer):
    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        return self.formula


@dataclass(frozen=True)
class EventuallyTimer(Timer):
    child: Timer

    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        return timer_finite(self.child.term(sym, params))

    def transition(
        self, pre_sym: Sym, post_sym: Sym, params: Params
    ) -> None | z3.BoolRef:
        return timer_zero(self.term(pre_sym, params)) == z3.Or(
            timer_zero(self.child.term(pre_sym, params)),
            timer_zero(self.term(post_sym, params)),
        )


@dataclass(frozen=True)
class GloballyTimer(Timer):
    child: Timer
    negated_child: Timer

    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        return timer_infinite(self.negated_child.term(sym, params))

    def transition(
        self, pre_sym: Sym, post_sym: Sym, params: Params
    ) -> None | z3.BoolRef:
        return timer_zero(self.term(pre_sym, params)) == z3.And(
            timer_zero(self.child.term(pre_sym, params)),
            timer_zero(self.term(post_sym, params)),
        )


@dataclass(frozen=True)
class NegationTimer(Timer):
    child: Timer

    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        return timer_nonzero(self.child.term(sym, params))


@dataclass(frozen=True)
class ConjunctionTimer(Timer):
    children: tuple[Timer, ...]

    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        return z3.And(*(timer_zero(child.term(sym, params)) for child in self.children))


@dataclass(frozen=True)
class DisjunctionTimer(Timer):
    children: tuple[Timer, ...]

    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        return z3.Or(*(timer_zero(child.term(sym, params)) for child in self.children))


@dataclass(frozen=True)
class ImplicationTimer(Timer):
    antecedent: Timer
    consequent: Timer

    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        return z3.Implies(
            timer_zero(self.antecedent.term(sym, params)),
            timer_zero(self.consequent.term(sym, params)),
        )


@dataclass(frozen=True)
class ForallTimer(Timer):
    body: Timer
    vars: ParamSpec

    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        vars_params = {var: z3.Const(var, sort) for var, sort in self.vars.items()}
        all_params = params | vars_params
        return z3.ForAll(list(vars_params.values()), self.body.term(sym, all_params))


@dataclass(frozen=True)
class ExistsTimer(Timer):
    body: Timer
    vars: ParamSpec

    def axiom(self, sym: Sym, params: Params) -> z3.BoolRef:
        vars_params = {var: z3.Const(var, sort) for var, sort in self.vars.items()}
        all_params = params | vars_params
        return z3.Exists(list(vars_params.values()), self.body.term(sym, all_params))


def create_timers(root_formula: z3.BoolRef, ts: TransitionSystem) -> dict[TimerId, Timer]:

    timers: dict[TimerId, Timer] = {}

    def add(timer: Timer) -> Timer:
        timers[timer.id] = timer
        return timer

    def create_timer(formula: z3.ExprRef) -> Timer:
        assert isinstance(formula, z3.BoolRef)
        if z3.is_quantifier(formula) and formula.is_exists():
            variables, body = unpack_quantifier(formula)
            body_timer = create_timer(body)
            return add(
                ExistsTimer(
                    formula,
                    str(formula),
                    body_timer.params,
                    body_timer,
                    {str(var): var.sort() for var in variables},
                )
            )
        elif z3.is_quantifier(formula) and formula.is_forall():
            variables, body = unpack_quantifier(formula)
            body_timer = create_timer(body)
            variables_params = {str(var): var.sort() for var in variables}
            return add(
                ForallTimer(
                    formula,
                    str(formula),
                    {
                        param: sort
                        for param, sort in body_timer.params.items()
                        if param not in variables_params
                    },
                    body_timer,
                    variables_params,
                )
            )
        elif z3.is_implies(formula):
            ante, consq = formula.children()
            ante_timer = create_timer(ante)
            consq_timer = create_timer(consq)
            return add(
                ImplicationTimer(
                    formula,
                    str(formula),
                    ante_timer.params | consq_timer.params,
                    ante_timer,
                    consq_timer,
                )
            )
        elif z3.is_or(formula):
            children = tuple(create_timer(child) for child in formula.children())
            return add(
                DisjunctionTimer(
                    formula,
                    str(formula),
                    reduce(operator.or_, (child.params for child in children)),
                    children,
                )
            )
        elif z3.is_and(formula):
            children = tuple(create_timer(child) for child in formula.children())
            return add(
                ConjunctionTimer(
                    formula,
                    str(formula),
                    reduce(operator.or_, (child.params for child in children)),
                    children,
                )
            )
        elif z3.is_not(formula):
            (child,) = formula.children()
            child_timer = create_timer(child)
            return add(
                NegationTimer(formula, str(formula), child_timer.params, child_timer)
            )
        elif z3.is_app(formula) and formula.decl().eq(G):
            (child,) = formula.children()
            negated_child = normalized_not(child)

            child_timer = create_timer(child)
            negated_child_timer = create_timer(negated_child)

            return add(
                GloballyTimer(
                    formula,
                    str(formula),
                    child_timer.params,
                    child_timer,
                    negated_child_timer,
                )
            )
        elif z3.is_app(formula) and formula.decl().eq(F):
            (child,) = formula.children()
            child_timer = create_timer(child)
            return add(
                EventuallyTimer(formula, str(formula), child_timer.params, child_timer)
            )
        else:  # if nothing else then atomic
            atomic_params = get_params(formula, set(ts.symbols.keys()))
            return add(AtomicTimer(formula, str(formula), atomic_params))

    _root_timer = create_timer(root_formula)

    return timers


def get_params(root_expr: z3.ExprRef, excluded: set[str]) -> ParamSpec:
    params: ParamSpec = {}

    def find_params(expr: z3.ExprRef) -> None:
        if (
            z3.is_const(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and expr.decl().name() not in excluded
        ):
            params[expr.decl().name()] = expr.sort()
        else:
            for child in expr.children():
                find_params(child)

    find_params(root_expr)
    return params


def normalized_not(formula: z3.ExprRef) -> z3.BoolRef:
    assert isinstance(formula, z3.BoolRef)
    if z3.is_not(formula):
        (child,) = formula.children()
        return cast(z3.BoolRef, child)
    else:
        return z3.Not(formula)


def clone_vars(quantifier: z3.QuantifierRef) -> list[z3.ExprRef]:
    return [
        z3.Const(quantifier.var_name(i), quantifier.var_sort(i))
        for i in range(quantifier.num_vars())
    ]


def unpack_quantifier(
    quantifier: z3.QuantifierRef,
) -> tuple[list[z3.ExprRef], z3.BoolRef]:
    bounding_vars = clone_vars(quantifier)

    body = z3.substitute_vars(
        quantifier.body(), *reversed(bounding_vars)
    )  # Z3 uses vars in reverse order

    return bounding_vars, body
