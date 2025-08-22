from typing import Annotated

import z3

from better_ts import TransitionSystem, axiom, transition, invariant
from z3_sorted import SortedExpr, Rel, Const
from new_timers import F, G, create_timers


class Thread(SortedExpr): ...


class Ticket(SortedExpr): ...


X, Y, Z, K, K1, K2, M = Ticket.consts("X Y Z K K1 K2 M")
T, T1, T2 = Thread.consts("T T1 T2")


class TicketSystem(TransitionSystem):
    zero: Annotated[Const, Ticket, "immutable"]
    service: Annotated[Const, Ticket]
    next_ticket: Annotated[Const, Ticket]
    skolem_thread: Annotated[Const, Thread, "immutable"]

    pc1: Annotated[Rel, Thread]
    pc2: Annotated[Rel, Thread]
    pc3: Annotated[Rel, Thread]
    m: Annotated[Rel, Thread, Ticket]
    le: Annotated[Rel, Ticket, Ticket, "immutable"]
    scheduled: Annotated[Rel, Thread]

    def succ(self, u: z3.ExprRef, v: z3.ExprRef) -> z3.BoolRef:
        return z3.And(
            self.le(u, v),
            z3.Not(u == v),
            z3.ForAll(X, z3.Implies(self.le(u, X), z3.Or(self.le(v, X), X == u))),
        )

    @axiom
    def order_le(self) -> z3.BoolRef:
        return z3.And(
            # transitive, antisymmetric and total, with zero as minimal
            z3.ForAll(
                [X, Y, Z],
                z3.Implies(z3.And(self.le(X, Y), self.le(Y, Z)), self.le(X, Z)),
            ),
            z3.ForAll([X, Y], z3.Implies(z3.And(self.le(X, Y), self.le(Y, X)), X == Y)),
            z3.ForAll([X, Y], z3.Or(self.le(X, Y), self.le(Y, X))),
            z3.ForAll(X, self.le(self.zero, X)),
        )

    @axiom
    def scheduling(self):
        return z3.ForAll(
            [T1, T2],
            z3.Implies(z3.And(self.scheduled(T1), self.scheduled(T2)), T1 == T2),
        )

    def init(self):
        return z3.And(
            z3.ForAll(T, self.pc1(T)),
            z3.ForAll(T, z3.Not(self.pc2(T))),
            z3.ForAll(T, z3.Not(self.pc3(T))),
            self.service == self.zero,
            self.next_ticket == self.zero,
            z3.ForAll([T, X], self.m(T, X) == (X == self.zero)),
            z3.ForAll(T, z3.Not(self.scheduled(T))),
        )

    @transition
    def step12(self, t: Thread) -> z3.BoolRef:
        return z3.And(
            # guard
            self.scheduled(t),  # not sure this works
            self.pc1(t),
            # updates
            z3.ForAll(
                [T, X],
                self.next["m"](T, X)
                == z3.If(T == t, X == self.next_ticket, self.m(T, X)),
            ),
            z3.ForAll(T, self.next.pc1(T) == z3.And(T != t, self.pc1(T))),
            z3.ForAll(T, self.next.pc2(T) == z3.Or(T == t, self.pc2(T))),
            z3.ForAll(T, self.next.pc3(T) == self.pc3(T)),
            self.next.service == self.service,
            self.succ(self.next_ticket, self.next.next_ticket),
        )

    @transition
    def step22(self, t: Thread, k: Ticket) -> z3.BoolRef:
        return z3.And(
            # guard
            self.scheduled(t),  # z3.Not sure this works
            self.pc2(t),
            self.m(t, k),
            z3.Not(self.le(k, self.service)),
            # updates
            z3.ForAll(T, self.next.pc1(T) == self.pc1(T)),
            z3.ForAll(T, self.next.pc2(T) == self.pc2(T)),
            z3.ForAll(T, self.next.pc3(T) == self.pc3(T)),
            z3.ForAll([T, X], self.next.m(T, X) == self.m(T, X)),
            self.next.service == self.service,
            self.next.next_ticket == self.next_ticket,
        )

    @transition
    def step23(self, t: Thread, k: Ticket) -> z3.BoolRef:
        return z3.And(
            # guard
            self.scheduled(t),  # not sure this works
            self.pc2(t),
            self.m(t, k),
            self.le(k, self.service),
            # updates
            z3.ForAll(T, self.next.pc1(T) == self.pc1(T)),
            z3.ForAll(T, self.next.pc2(T) == z3.And(T != t, self.pc2(T))),
            z3.ForAll(T, self.next.pc3(T) == z3.Or(T == t, self.pc3(T))),
            z3.ForAll([T, X], self.next.m(T, X) == self.m(T, X)),
            self.next.service == self.service,
            self.next.next_ticket == self.next_ticket,
        )

    @transition
    def step31(self, t: Thread) -> z3.BoolRef:
        return z3.And(
            # guard
            self.scheduled(t),  # not sure this works
            self.pc3(t),
            # updates
            z3.ForAll(T, self.next.pc1(T) == z3.Or(T == t, self.pc1(T))),
            z3.ForAll(T, self.next.pc2(T) == self.pc2(T)),
            z3.ForAll(T, self.next.pc3(T) == z3.And(T != t, self.pc3(T))),
            z3.ForAll([T, X], self.next.m(T, X) == self.m(T, X)),
            self.succ(self.service, self.next.service),
            self.next.next_ticket == self.next_ticket,
        )

    @invariant
    def at_least_one_pc(self) -> z3.BoolRef:
        return z3.ForAll(T, z3.Or(self.pc1(T), self.pc2(T), self.pc3(T)))

    @invariant
    def at_most_one_pc(self) -> z3.BoolRef:
        return z3.ForAll(
            T,
            z3.And(
                z3.Not(z3.And(self.pc1(T), self.pc2(T))),
                z3.Not(z3.And(self.pc1(T), self.pc3(T))),
                z3.Not(z3.And(self.pc2(T), self.pc3(T))),
            ),
        )

    @invariant
    def one_thread_per_ticket(self) -> z3.BoolRef:
        return z3.ForAll(
            [T, K1, K2], z3.Implies(z3.And(self.m(T, K1), self.m(T, K2)), K1 == K2)
        )

    def temporal_property(self) -> z3.BoolRef:
        return z3.And(
            z3.ForAll(T, G(F(self.scheduled(T)))),
            F(
                z3.And(
                    self.pc2(self.skolem_thread),
                    G(z3.Not(self.pc3(self.skolem_thread))),
                )
            ),
        )


def ticket():

    transitions = [tr_step12, tr_step22, tr_step23, tr_step31]
    ts = TS(sorts, axiom, init, transitions, constant_sym, relation_sym, function_sym)

    scheduled = z3.Function("scheduled", Thread, z3.BoolSort())
    skolem_thread = z3.Const("skolem_thread", Thread)
    pc2 = z3.Function("pc2", Thread, z3.BoolSort())
    pc3 = z3.Function("pc3", Thread, z3.BoolSort())

    simplified_formula = foltl_nnf(
        And(
            ForAll(T, G(F(scheduled(T)))),
            F(And(pc2(skolem_thread), G(Not(pc3(skolem_thread))))),
        )
    )
    # non-negated property
    formula = foltl_nnf(
        z3.Not(
            Implies(
                ForAll(T, G(F(scheduled(T)))), ForAll(T, G(Implies(pc2(T), F(pc3(T)))))
            )
        )
    )
    # user can write timer for Not(G(Implies(pc2(T),F(pc3(T))))

    # here we only give the def. of the skolem thread and not use it directly.
    formula = foltl_nnf(
        z3.Not(
            Implies(
                Implies(
                    Exists(T, F(And(pc2(T), G(Not(pc3(T)))))),
                    F(And(pc2(skolem_thread), G(Not(pc3(skolem_thread))))),
                ),
                Implies(
                    ForAll(T, G(F(scheduled(T)))),
                    ForAll(T, G(Implies(pc2(T), F(pc3(T))))),
                ),
            )
        )
    )

    timer_system = timer_transition_system(
        simplified_formula, {"skolem_thread": Thread}
    )
    print(timer_system.constant_sym)
    intersection = IntersectionTS(ts, timer_system)

    # system invariant
    def system_invariant(sym):
        return And(
            ForAll(T, Or(sym["pc1"](T), sym["pc2"](T), sym["pc3"](T))),
            ForAll(T, Or(Not(sym["pc1"](T)), Not(sym["pc2"](T)))),
            ForAll(T, Or(Not(sym["pc1"](T)), Not(sym["pc3"](T)))),
            ForAll(T, Or(Not(sym["pc2"](T)), Not(sym["pc3"](T)))),
            ForAll(
                [T, K1, K2], Implies(And(sym["m"](T, K1), sym["m"](T, K2)), K1 == K2)
            ),
            ForAll(
                [T1, T2], Implies(And(sym["pc3"](T1), sym["pc3"](T2)), T1 == T2)
            ),  # safety
            ForAll(
                T, Implies(sym["next_ticket"] == sym["zero"], sym["m"](T, sym["zero"]))
            ),
            ForAll(
                [T, M],
                Implies(
                    And(sym["next_ticket"] != sym["zero"], sym["m"](T, M)),
                    Not(sym["le"](sym["next_ticket"], M)),
                ),
            ),
            ForAll(
                T,
                Implies(
                    Or(sym["pc2"](T), sym["pc3"](T)), sym["next_ticket"] != sym["zero"]
                ),
            ),
            ForAll(
                [T1, T2, M],
                Implies(
                    And(sym["m"](T1, M), sym["m"](T2, M), M != sym["zero"]), T1 == T2
                ),
            ),
            ForAll(
                [T, M],
                Implies(
                    And(sym["pc2"](T), sym["m"](T, M)), sym["le"](sym["service"], M)
                ),
            ),
            ForAll(T, Implies(sym["pc3"](T), sym["m"](T, sym["service"]))),
            sym["le"](sym["service"], sym["next_ticket"]),
            ForAll(
                [T1, T2],
                Not(
                    And(
                        Not(sym["pc1"](T1)),
                        Not(sym["pc1"](T2)),
                        sym["m"](T1, sym["zero"]),
                        sym["m"](T2, sym["zero"]),
                        T1 != T2,
                    )
                ),
            ),
            ForAll(
                [T, M],
                Implies(
                    And(sym["pc1"](T), sym["m"](T, M), M != sym["zero"]),
                    Not(sym["le"](sym["service"], M)),
                ),
            ),
            ForAll(
                K,
                Implies(
                    And(
                        Not(sym["le"](sym["next_ticket"], K)),
                        sym["le"](sym["service"], K),
                    ),
                    Exists(T, And(sym["m"](T, K), Not(sym["pc1"](T)))),
                ),
            ),
            Exists(M, sym["m"](sym["skolem_thread"], M)),
        )

    # timer invariant
    # you would be able to clean up the invariant if the timers had more precise semantics
    def timer_invariant(sym):
        return And(
            ForAll(
                T, sym["t_<G(F(scheduled(T)))>"](T) == 0
            ),  # ForAll(T,G(F(scheduled(T)))
            Or(
                sym["t_<And(pc2(skolem_thread), G(Not(pc3(skolem_thread))))>"]
                >= 0,  # F(And(...))
                And(
                    sym["t_<G(Not(pc3(skolem_thread)))>"] == 0,  # G(...)
                    sym["pc2"](sym["skolem_thread"]),
                    # sym['t_<pc2(skolem_thread)>']==0 #such an invariant doesn't hold without the better implementation of timers - equivalent to the one above
                    ForAll(
                        K,
                        Implies(
                            sym["m"](sym["skolem_thread"], K),
                            sym["le"](sym["service"], K),
                        ),
                    ),
                ),
            ),
        )

    # maybe the user gives this as a temporal_invariant()

    invariant = lambda sym: And(system_invariant(sym), timer_invariant(sym))

    # system rank
    # difference in ticket between ticket of violating node? and service
    # something about position of nodes
    param_k = {"k": Ticket}
    between_service_and_skolem_ticket = lambda sym, param: And(
        sym["le"](sym["service"], param["k"]),
        Exists(K, And(sym["m"](sym["skolem_thread"], K), sym["le"](param["k"], K))),
    )
    bin = BinaryFreeRank(between_service_and_skolem_ticket, param_k)
    diff_ticket_service = ParPointwiseFreeRank(bin, param_k)

    param_t = {"t": Thread}
    active = lambda sym, param: sym["m"](param["t"], sym["service"])
    not_active = lambda sym, param: Not(active(sym, param))
    not_pc3 = lambda sym, param: Not(sym["pc3"](param["t"]))
    bin_not_pc3 = BinaryFreeRank(not_pc3, param_t)
    number_not_pc3 = ParPointwiseFreeRank(bin_not_pc3, param_t)

    system_rank = LexFreeRank([diff_ticket_service, number_not_pc3])

    # timer rank
    # timers of the scheduling of the node that holds the service
    # possibly something else small

    param_int = {"x": IntSort()}
    scheduled_timer = PositionInOrderFreeRank(
        lambda sym, param1, param2: param1["x"] < param2["x"],
        param_int,
        {"x": lambda sym, param: sym["t_<scheduled(T)>"](param["t"])},
    )
    trivial_rank = BinaryFreeRank(lambda *args: True, param_t)
    timer_for_active = LinFreeRank(
        [scheduled_timer, trivial_rank], [active, not_active]
    )
    all_active_sched_timers = ParPointwiseFreeRank(timer_for_active, param_t)

    trigger_timer = PositionInOrderFreeRank(
        lambda sym, param1, param2: param1["x"] < param2["x"],
        param_int,
        {
            "x": lambda sym, param: sym[
                "t_<And(pc2(skolem_thread), G(Not(pc3(skolem_thread))))>"
            ]
        },
    )

    after_trigger = lambda sym, param: And(
        sym["t_<G(Not(pc3(skolem_thread)))>"] == 0, sym["pc2"](sym["skolem_thread"])
    )
    before_trigger = lambda sym, param: Not(after_trigger(sym, param))

    system_and_scheduling_rank = LexFreeRank(
        [system_rank, all_active_sched_timers],
    )

    rank = LinFreeRank(
        [trigger_timer, system_and_scheduling_rank], [before_trigger, after_trigger]
    )

    proof = TerminationProof(rank, invariant)
    proof.check_proof(intersection)


# ticket()

sys = TicketSystem()
sys.check_invariants()

# result = create_timers(sys.temporal_property(), sys)
#
# print(result)
