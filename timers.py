import operator
from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass
from functools import cached_property, reduce
from typing import cast, overload, Any, Self, Literal

import z3

from rewriter import rewrite
from ts import TS, FreeRank, print_model_in_order, PositionInOrderFreeRank

G = z3.Function("G", z3.BoolSort(), z3.BoolSort())
F = z3.Function("F", z3.BoolSort(), z3.BoolSort())

temporal_operators = [G, F]

false = z3.BoolVal(False)
true = z3.BoolVal(True)


def clone_vars(quantifier: z3.QuantifierRef) -> list[z3.Const]:
    return [
        z3.Const(quantifier.var_name(i), quantifier.var_sort(i))
        for i in range(quantifier.num_vars())
    ]


def unpack_quantifier(
        quantifier: z3.QuantifierRef,
) -> tuple[list[z3.Const], z3.BoolRef]:
    bounding_vars = clone_vars(quantifier)

    body = z3.substitute_vars(
        quantifier.body(), *reversed(bounding_vars)
    )  # Z3 uses vars in reverse order

    return bounding_vars, body


@overload
def rename_symbol(symbol: z3.ExprRef, name: str | None = None) -> z3.ExprRef:
    ...


@overload
def rename_symbol(symbol: z3.FuncDeclRef, name: str | None = None) -> z3.FuncDeclRef:
    ...


def rename_symbol(symbol: z3.ExprRef | z3.FuncDeclRef, name: str | None = None) -> z3.ExprRef | z3.FuncDeclRef:
    if name is None:
        name = str(symbol) + "'"
    if isinstance(symbol, z3.FuncDeclRef):
        signature = [symbol.domain(i) for i in range(symbol.arity())] + [symbol.range()]
        return z3.Function(name, *signature)
    else:
        return z3.Const(name, symbol.sort())



def foltl_nnf(formula: z3.BoolRef, negated: bool = False) -> z3.BoolRef:
    if z3.is_false(formula):
        if negated:
            return true
        else:
            return false
    elif z3.is_true(formula):
        if negated:
            return false
        else:
            return true
    elif z3.is_quantifier(formula):
        variables, body = unpack_quantifier(formula)
        nnf_body = foltl_nnf(body, negated)
        if (negated and formula.is_forall()) or (not negated and formula.is_exists()):
            return z3.Exists(variables, nnf_body)
        else:
            return z3.ForAll(variables, nnf_body)
    elif formula.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        decl = formula.decl()
        if decl in temporal_operators:
            body = cast(z3.BoolRef, formula.children()[0])
            nnf_body = foltl_nnf(body, negated)
            if (negated and decl == G) or (not negated and decl == F):
                return F(nnf_body)
            else:
                return G(nnf_body)
        if negated:
            return z3.Not(formula)
        else:
            return formula
    elif z3.is_eq(formula):
        left, right = cast(list[z3.BoolRef], formula.children())
        if z3.is_bool(left):  # iff construction
            return foltl_nnf(
                z3.And(z3.Implies(left, right), z3.Implies(right, left)), negated
            )
        else:
            return formula
    elif z3.is_distinct(formula):
        left, right = cast(list[z3.BoolRef], formula.children())
        if z3.is_bool(left):  # not-iff construction
            return foltl_nnf(
                z3.And(z3.Implies(left, right), z3.Implies(right, left)), not negated
            )
        else:
            return formula
    elif z3.is_not(formula):
        body = cast(z3.BoolRef, formula.children()[0])
        return foltl_nnf(body, not negated)
    elif z3.is_and(formula) or z3.is_or(formula):
        children = [
            foltl_nnf(cast(z3.BoolRef, child), negated) for child in formula.children()
        ]
        if (negated and z3.is_and(formula)) or (not negated and z3.is_or(formula)):
            return z3.Or(*children)
        else:
            return z3.And(*children)
    elif z3.is_implies(formula):
        antecedent, consequent = cast(list[z3.BoolRef], formula.children())
        return foltl_nnf(z3.Or(z3.Not(antecedent), consequent), negated)

    raise ValueError(f"Unexpected formula: {formula}")


def forall_if_vars(variables: list[z3.Const], body: z3.BoolRef) -> z3.BoolRef:
    if len(variables) > 0:
        return z3.ForAll(variables, body)
    else:
        return body


type SymSpec = dict[str, tuple[z3.SortRef, ...]]
type Sym = dict[str, z3.ExprRef | z3.FuncDeclRef]


def calculate_sym_rec(expr: z3.ExprRef, result: Sym) -> None:
    if z3.is_app(expr):
        decl = expr.decl()
        if decl.kind() == z3.Z3_OP_UNINTERPRETED and decl not in temporal_operators:
            if z3.is_const(expr):
                result[decl.name()] = expr
            else:
                result[decl.name()] = decl
    for child in expr.children():
        calculate_sym_rec(child, result)


def calculate_sym(expr: z3.ExprRef) -> Sym:
    result = {}
    calculate_sym_rec(expr, result)
    return result


def prime_sym(sym: Sym) -> Sym:
    return {name: rename_symbol(symbol) for name, symbol in sym.items()}


def reset_sym(sym: Sym) -> Sym:
    return {name: rename_symbol(symbol, name) for name, symbol in sym.items()}


def rewrite_expr(expr: z3.ExprRef, sym1: Sym, sym2: Sym | None = None) -> z3.ExprRef:
    if sym2 is None:
        sym2 = sym1
        sym1 = reset_sym(sym1)

    for name, pre in sym1.items():
        post = sym2[name]
        if isinstance(pre, z3.FuncDeclRef):
            args = [z3.FreshConst(pre.domain(i)) for i in range(pre.arity())]
            args_reversed = list(reversed(args))
            term = z3.Lambda(args_reversed, post(*args)).body()
            expr = rewrite(expr, pre, term)
        else:
            expr = rewrite(expr, pre.decl(), post)
    return expr


class Timer(ABC):
    def expr(self, sym: Sym) -> z3.ArithRef:
        timer = sym[f"t_{self}"]
        if self.variables:
            return cast(z3.ArithRef, timer(*self.variables.values()))
        else:
            return timer

    def quantified_axiom(self, sym: Sym) -> z3.BoolRef:
        return forall_if_vars(list(self.variables.values()), self._axiom(sym))

    @abstractmethod
    def _axiom(self, sym: Sym) -> z3.BoolRef:
        ...

    @property
    @abstractmethod
    def children(self) -> tuple["Timer", ...]:
        ...

    @property
    @abstractmethod
    def free_variables(self) -> dict[str, z3.SortRef]:
        ...

    @property
    def variables(self) -> dict[str, z3.ExprRef]:
        return {name: z3.Const(name, sort) for name, sort in self.free_variables.items()}

    @property
    def timer_spec(self) -> tuple[str, tuple[z3.SortRef, ...]]:
        sorts = list(self.free_variables.values())
        return f"t_{self}", tuple(sorts + [z3.IntSort()])

    @property
    def dict_spec(self) -> SymSpec:
        name, spec = self.timer_spec
        dict_spec = {name: spec}
        for child in self.children:
            for name, spec in child.dict_spec.items():
                dict_spec[name] = spec

        return dict_spec

    def quantified_transition(self, sym1: Sym, sym2: Sym) -> z3.BoolRef:
        return forall_if_vars(list(self.variables.values()), self._transition(sym1, sym2))

    def _transition(self, sym1: Sym, sym2: Sym) -> z3.BoolRef:
        return z3.Implies(
            self.expr(sym1) > 0,
            self.expr(sym2) == self.expr(sym1) - 1
        )


def is_free_variable(expr: z3.ExprRef) -> bool:
    return (
            z3.is_const(expr)
            and not z3.is_bool(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
    )


def free_variables(expr: z3.ExprRef) -> dict[str, z3.SortRef]:
    if is_free_variable(expr):
        return {expr.decl().name(): expr.sort()}
    return reduce(operator.or_, map(free_variables, expr.children()), {})


@dataclass(frozen=True)
class PropTimer(Timer):
    prop: z3.BoolRef
    sym: Sym

    def _axiom(self, sym: Sym) -> z3.BoolRef:
        return z3.Implies(self.expr(sym) == 0, rewrite_expr(self.prop, sym))

    @cached_property
    def children(self) -> tuple["Timer", ...]:
        return tuple()

    @cached_property
    def free_variables(self) -> dict[str, z3.SortRef]:
        return {name: sort for name, sort in free_variables(self.prop).items() if name not in self.sym}

    def __str__(self) -> str:
        return f"<{self.prop}>"


@dataclass(frozen=True)
class BoolOpTimer(Timer):
    child_timers: tuple[Timer, ...]
    is_and: bool

    def _axiom(self, sym: Sym) -> z3.BoolRef:
        if self.is_and:
            op = z3.And
        else:
            op = z3.Or
        return z3.Implies(
            self.expr(sym) == 0,
            op(*[child.expr(sym) == 0 for child in self.children]),
        )

    @cached_property
    def children(self) -> tuple["Timer", ...]:
        return self.child_timers

    @cached_property
    def free_variables(self) -> dict[str, z3.SortRef]:
        return reduce(
            operator.or_,
            map(lambda timer: timer.free_variables, self.child_timers),
            {},
        )

    def __str__(self) -> str:
        if self.is_and:
            op = "∧"
        else:
            op = "∨"
        children = f" {op} ".join(str(child) for child in self.child_timers)
        return f"({children})"


@dataclass(frozen=True)
class GloballyTimer(Timer):
    body: Timer

    def _axiom(self, sym: Sym) -> z3.BoolRef:
        return z3.Implies(self.expr(sym) == 0, self.body.expr(sym) == 0)

    def _transition(self, sym1: Sym, sym2: Sym) -> z3.BoolRef:
        return z3.And(super()._transition(sym1, sym2), z3.Implies(self.expr(sym1) == 0, self.expr(sym2) == 0))

    @cached_property
    def children(self) -> tuple["Timer", ...]:
        return (self.body,)

    @cached_property
    def free_variables(self) -> dict[str, z3.SortRef]:
        return self.body.free_variables

    def __str__(self) -> str:
        return f"G{self.body}"


@dataclass(frozen=True)
class EventuallyTimer(Timer):
    body: Timer

    def _axiom(self, sym: Sym) -> z3.BoolRef:
        return z3.Implies(self.expr(sym) == 0, self.body.expr(sym) >= 0)

    @cached_property
    def children(self) -> tuple["Timer", ...]:
        return (self.body,)

    @cached_property
    def free_variables(self) -> dict[str, z3.SortRef]:
        return self.body.free_variables

    def __str__(self) -> str:
        return f"F{self.body}"


@dataclass(frozen=True)
class QuantifierTimer(Timer):
    body: Timer
    is_forall: bool
    quantifier_variables: dict[str, z3.SortRef]

    def _axiom(self, sym: Sym) -> z3.BoolRef:
        if self.is_forall:
            quantifier = z3.ForAll
        else:
            quantifier = z3.Exists
        variables = [z3.Const(name, sort) for name, sort in self.quantifier_variables.items()]
        return z3.Implies(
            self.expr(sym) == 0,
            quantifier(variables, self.body.expr(sym) == 0),
        )

    @cached_property
    def children(self) -> tuple["Timer", ...]:
        return (self.body,)

    @cached_property
    def free_variables(self) -> dict[str, z3.SortRef]:
        return {key: value for key, value in self.body.free_variables.items() if key not in self.quantifier_variables}

    def __str__(self) -> str:
        if self.is_forall:
            quantifier = "∀"
        else:
            quantifier = "∃"
        variables = ",".join(str(var) for var in self.quantifier_variables)
        return f"{quantifier}{variables}.{self.body}"


def construct_timer(formula: z3.BoolRef, sym: Sym) -> Timer | None:
    """Assuming that {formula} is in NNF"""
    if z3.is_or(formula) or z3.is_and(formula):
        all_none = True
        maybe_child_timers = []
        for child in formula.children():
            child_timer = construct_timer(cast(z3.BoolRef, child), sym)
            if child_timer is not None:
                all_none = False
            maybe_child_timers.append(child_timer)

        if all_none:
            return None

        child_timers = []
        for child, timer in zip(formula.children(), maybe_child_timers):
            if timer is not None:
                child_timers.append(timer)
            else:
                child_timers.append(PropTimer(child, sym))
        return BoolOpTimer(tuple(child_timers), z3.is_and(formula))
    elif z3.is_quantifier(formula):
        variables, body = unpack_quantifier(formula)
        body_timer = construct_timer(body, sym)
        if body_timer is None:
            return None
        return QuantifierTimer(body_timer, formula.is_forall(), {var.decl().name(): var.sort() for var in variables})
    elif (
            formula.decl().kind() == z3.Z3_OP_UNINTERPRETED
            and formula.decl() in temporal_operators
    ):
        body = formula.children()[0]
        child_timer = construct_timer(cast(z3.BoolRef, body), sym)
        if child_timer is None:
            child_timer = PropTimer(body, sym)
        if formula.decl() == G:
            return GloballyTimer(child_timer)
        else:
            return EventuallyTimer(child_timer)
    else:
        return None


def timers(root: Timer) -> list[Timer]:
    return [root] + reduce(operator.add, map(timers, root.children), list())


def sym_from_sym_spec(sym_spec: SymSpec, suffix: str = "") -> Sym:
    def sym_from_spec(name: str, spec: tuple[z3.SortRef, ...]) -> z3.ExprRef | z3.FuncDeclRef:
        if len(spec) == 0:
            return z3.Bool(name)
        elif len(spec) == 1:
            return z3.Const(name, spec[0])
        else:
            return z3.Function(name, *spec)

    return {
        name: sym_from_spec(name, spec)
        for name, spec in sym_spec.items()
    }


def timer_transition_system(formula: z3.BoolRef, given_sym: Sym) -> TS:
    root = construct_timer(formula, given_sym)

    all_timers = timers(root)

    def axiom(sym: Sym) -> z3.BoolRef:
        return z3.And(*[
            timer.quantified_axiom(sym)
            for timer in all_timers
        ])

    def init(sym: Sym) -> z3.BoolRef:
        return root.expr(sym) == 0

    def transition(sym1: Sym, sym2: Sym, _param) -> z3.BoolRef:
        return z3.And(*[
            timer.quantified_transition(sym1, sym2)
            for timer in all_timers
        ])

    sym = calculate_sym(formula) | sym_from_sym_spec(root.dict_spec)
    constants = {
        name: symbol.sort()
        for name, symbol in sym.items()
        if not isinstance(symbol, z3.FuncDeclRef)
    }
    rels = {
        name: [symbol.domain(i) for i in range(symbol.arity())]
        for name, symbol in sym.items()
        if isinstance(symbol, z3.FuncDeclRef) and symbol.range().eq(z3.BoolSort())
    }
    funs = {
        name: [symbol.domain(i) for i in range(symbol.arity())] + [symbol.range()]
        for name, symbol in sym.items()
        if isinstance(symbol, z3.FuncDeclRef) and not symbol.range().eq(z3.BoolSort())
    }

    sorts = set()
    for symbol in sym.values():
        if isinstance(symbol, z3.FuncDeclRef):
            sorts.add(symbol.range())
            for i in range(symbol.arity()):
                sorts.add(symbol.domain(i))
        else:
            sorts.add(symbol.sort())

    sorts -= {z3.BoolSort(), z3.IntSort()}

    transitions = [("timers", {}, transition)]

    return TS(list(sorts), axiom, init, transitions, constants, rels, funs)


class IntersectionTS(TS):
    def __init__(self, ts1: TS, ts2: TS) -> None:
        self.sorts = list(set(ts1.sorts) | set(ts2.sorts))
        self.axiom = lambda sym: z3.And(ts1.axiom(sym), ts2.axiom(sym))
        self.init = lambda sym: z3.And(ts1.init(sym), ts2.init(sym))
        self.transitions = []  # todo: should be product of ts1.transitions and ts2.transitions
        self.tr = lambda sym1, sym2: z3.And(ts1.tr(sym1, sym2), ts2.tr(sym1, sym2))
        self.constant_sym = ts1.constant_sym | ts2.constant_sym
        self.relation_sym = ts1.relation_sym | ts2.relation_sym
        self.function_sym = ts1.function_sym | ts2.function_sym

@dataclass
class TerminationProof:
    rank: FreeRank
    theta: Callable[[Sym], z3.BoolRef]

    def check_proof(self, system: TS) -> bool:
        self.print_structure()
        if all((
            self.premise_inv(system),
            self.premise_reduced(system),
            self.premise_side(system)
        )):
            print("ok")
            return True
        else:
            print("fail")
            return False

    def print_structure(self) -> None:
        print("rank structure: ", end="")
        self.rank.print_structure()
        print()

    def premise_inv(self, system: TS) -> bool:
        return system.check_inductiveness(self.theta)

    def premise_reduced(self, system: TS) -> bool:
        state_pre = system.create_state("_pre")
        state_post = system.create_state("_post")

        states = [state_pre, state_post]

        tau = system.tr
        reduced = self.rank.reduced

        constraints = [
            self.theta(state_pre.get_dict()),
            tau(state_pre.get_dict(), state_post.get_dict()),
            z3.Not(reduced(state_pre.get_dict(), state_post.get_dict()))
        ]

        result, model = system.ts_sat_check(constraints, states)

        print(f"theta & tau -> rank' < rank: {result}")

        if result == z3.sat and model is not None:
            print_model_in_order(model, state_pre.get_sym() + state_post.get_sym())
            return False
        return result == z3.unsat

    def premise_side(self, system: TS) -> bool:
        rank_side_conditions = self.rank.side
        results = []
        for condition in rank_side_conditions:
            res = condition.finiteness_check(system)
            results.append(res)
        return all(results)


### Tests

def test_foltl_nnf() -> None:
    p = z3.Bool("p")
    q = z3.Function("q", z3.IntSort(), z3.BoolSort())
    r = z3.Bool("r")

    x = z3.Int("x")

    formula = z3.Not(G(z3.Or(p, z3.Implies(r, z3.ForAll(x, q(x))))))

    assert foltl_nnf(formula).eq(
        F(z3.And(z3.Not(p), z3.And(r, z3.Exists(x, z3.Not(q(x))))))
    )


def test_calculate_sym() -> None:
    p = z3.Bool("p")
    q = z3.Function("q", z3.IntSort(), z3.BoolSort())
    r = z3.Bool("r")

    x = z3.Int("x")

    formula = z3.Not(G(z3.Or(p, z3.Implies(r, z3.ForAll(x, q(x))))))

    sym = calculate_sym(formula)

    assert len(sym) == 3
    assert sym["p"].eq(p)
    assert sym["r"].eq(r)
    assert sym["q"].eq(q)


def test_rewrite_sym() -> None:
    p, pp, r, rp = z3.Bools("p p' r r'")
    q = z3.Function("q", z3.IntSort(), z3.BoolSort())
    qp = z3.Function("q'", z3.IntSort(), z3.BoolSort())

    x = z3.Int("x")

    formula = z3.Not(G(z3.Or(p, z3.Implies(r, z3.ForAll(x, q(x))))))

    sym1 = calculate_sym(formula)
    sym2 = prime_sym(sym1)

    result = rewrite_expr(formula, sym2)

    assert result.eq(z3.Not(G(z3.Or(pp, z3.Implies(rp, z3.ForAll(x, qp(x)))))))


def test_basic_timers() -> None:
    p = z3.Bool("p")
    S = z3.DeclareSort("S")
    q = z3.Function("q", S, z3.BoolSort())
    x = z3.Const("x", S)

    formula = z3.Or(G(p), z3.And(z3.ForAll(x, F(q(x))), F(p)))

    formula_sym = calculate_sym(formula)

    assert foltl_nnf(formula).eq(formula)

    print()
    root = construct_timer(formula, {})

    root_sym = sym_from_sym_spec(root.dict_spec) | formula_sym

    print(f"Init: {root.expr(root_sym) == 0}")
    for t in timers(root):
        print(t.expr(root_sym))
        print(t.quantified_axiom(root_sym))
        primed_sym = prime_sym(root_sym)
        print(t.quantified_axiom(primed_sym))


def test_timer_transition_system() -> None:
    S = z3.DeclareSort("S")
    c = z3.Const("c", S)
    q = z3.Function("q", S, z3.BoolSort())
    f = z3.Function("f", S, S)
    x = z3.Const("x", S)

    formula = z3.Or(G(q(c)), z3.And(z3.ForAll(x, F(q(f(x)))), F(q(c))))

    system = timer_transition_system(formula)

    pre_state = system.create_state("_pre")
    post_state = system.create_state("_post")
    sym_pre = pre_state.get_dict()
    sym_post = post_state.get_dict()

    print(system.axiom(sym_pre))
    print(system.axiom(sym_post))
    print(system.init(sym_pre))
    print(system.tr(sym_pre, sym_post))


def test_basic_system() -> None:
    S = z3.DeclareSort("S")

    sorts = [S]
    axiom = lambda sym: z3.BoolVal(True)
    init = lambda sym: sym["q"](sym["c"])
    transition = lambda sym1, sym2, _param: z3.And(
        sym1["q"](sym1["c"]),
        sym1["c"] == sym2["c"],
        sym2["q"](sym1["c"])
    )
    transitions = [("keep_q(c)", {}, transition)]
    constant_sym = {"c": S}
    function_sym = {}
    relation_sym = {"q": [S]}
    system = TS(sorts, axiom, init, transitions, constant_sym, relation_sym, function_sym)

    safety = lambda sym: sym["q"](sym["c"])
    system.check_init_maintains_inv(safety)
    system.check_tr_maintains_inv(safety)

    c = z3.Const("c", S)
    q = z3.Function("q", S, z3.BoolSort())
    formula = foltl_nnf(z3.Not(G(q(c))))


    timer_system = timer_transition_system(formula, {"c": c})

    intersection = IntersectionTS(system, timer_system)

    pre = intersection.create_state("_pre")
    pre_sym = pre.get_dict()
    post = intersection.create_state("_post")
    post_sym = post.get_dict()

    print("---Axioms---")
    print(intersection.axiom(pre_sym))
    print(intersection.axiom(post_sym))

    print("---Init---")
    print(intersection.init(pre_sym))

    print("---Transition---")
    print(intersection.tr(pre_sym, post_sym))

    param_order = {"x": z3.IntSort()}
    order = lambda sym, param1, param2: param1["x"] < param2["x"]
    rank = PositionInOrderFreeRank(order, param_order, {"x": lambda sym, param: sym["t_<Not(q(c))>"]})

    proof = TerminationProof(rank, lambda sym: sym["t_<Not(q(c))>"] >= 0)
    proof.check_proof(intersection)



# test_foltl_nnf()
# test_calculate_sym()
# test_rewrite_sym()
# test_basic_timers()
# test_timer_transition_system()
# test_basic_system()

