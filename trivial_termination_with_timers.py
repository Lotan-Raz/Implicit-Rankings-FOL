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
    
    #The system rank is the number of on nodes
    param_n = {'n':Node}
    on =  lambda sym, param:sym['on'](param['n'])
    not_on = lambda sym, param:Not(sym['on'](param['n']))
    bin = BinaryFreeRank(lambda sym, param:sym['on'](param['n']),param_n)
    number_of_on = ParPointwiseFreeRank(bin, param_n)

    #the number of on nodes is reduced when an on node is scheduled 
    #so we aggregate the timers of the on nodes
    param_int = {'x':IntSort()}	
    skd_timer = PositionInOrderFreeRank(
        lambda sym,param1,param2 : param1['x']<param2['x'],
        param_int,
        {'x':lambda sym,param:sym['t_<skd == X>'](param['n'])}
    )
    trivial_rank = BinaryFreeRank(lambda *args:True,param_n)
    timer_for_on = LinFreeRank(
        [skd_timer,trivial_rank],
        [on,not_on]
    )
    all_timers = ParPointwiseFreeRank(timer_for_on,param_n)

    rank = LexFreeRank([number_of_on,all_timers])

    timer_invariant = lambda sym: And(
        ForAll(X,sym['t_GF<skd == X>'](X)==0),
        #ForAll(X,sym['t_F<skd == X>'](X)==0), follows from previous
        sym['t_G<Exists(X, on(X))>']==0,
        #Exists(X,sym['on'](X)),
    )
    system_invariant = lambda sym: And()
    invariant = lambda sym: And(timer_invariant(sym),system_invariant(sym))

    proof = TerminationProof(rank,invariant)
    proof.check_proof(intersection)
    

trivial_termination_with_timers()