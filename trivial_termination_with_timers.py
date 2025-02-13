import z3
from z3 import *
from ts import *
from timers import *

def trivial_termination_with_timers():
    
    #This file presents the 'trivial termination' protocol where a network is comprised of a finite number of machines
    #The code for each machine is to terminate when it is scheduled for the first time
    #we want to show that under fair scheduling eventually all machines are terminated.
    #This is the solution to the exercise in TrivialTermination_Empty

    Node = DeclareSort('Node')
    X = Const('X',Node)
    sorts = [Node]

    constant_sym = {
        'skd' : Node,
    }
    relation_sym = {
        'on' : [Node],
    }
    function_sym = {
    }
    
    def axiom(sym):
        return True
    
    def init(sym):
        return ForAll(X,sym['on'](X))
    
    param_terminate = {}
    def terminate(sym1,sym2,param):
        return And(
            ForAll(X,sym2['on'](X)==And(sym1['on'](X),X!=sym1['skd']))
        )
    tr1 = ('tr1',param_terminate,terminate)

    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    skd = z3.Const("skd", Node)
    on = z3.Function("on", Node, z3.BoolSort())
    formula = foltl_nnf(z3.Not(z3.Implies(
        z3.ForAll(X, G(F(skd == X))),
        F(z3.ForAll(X, z3.Not(on(X))))
    )))

    timer_system = timer_transition_system(formula, {"skd": skd})

    intersection = IntersectionTS(ts, timer_system)

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


    #
    #
    #
    # r1 = lambda sym,param: sym['skd']==param['n']
    # p = true
    # q = lambda sym: ForAll(X,Not(sym['on'](X)))
    #
    # prop = LivenessProperty(p,q,[r1],[param_r1])
    #
    # rho = true
    # phi = lambda sym: And(rho(sym),Not(q(sym)))
    # psi = lambda sym,param: sym['on'](param['n'])
    #
    #
    # ##You need to find appropriate rank using the constructors
    param_r1 = {'n':Node}
    bin = BinaryFreeRank(lambda sym, param:sym['on'](param['n']),param_r1)
    number_of_on = ParPointwiseFreeRank(bin, param_r1)

    reduced = lambda sym1, sym2, param1, param2: z3.Or(
        z3.And(sym1["on"](param1["n"]), z3.Not(sym2["on"](param2["n"]))),
        sym2["t_<skd == X>"](param2["n"]) < sym1["t_<skd == X>"](param1["n"])
    )

    #
    # proof = LivenessProof(prop,rank,rho,phi,[psi])
    # proof.check_proof(ts)


trivial_termination_with_timers()