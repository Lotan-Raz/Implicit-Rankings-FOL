import z3
from z3 import *
from ts import *
from timers import *

def trivial_termination_with_timers():

    Node = DeclareSort('Node')
    X = Const('X',Node)
    sorts = [Node]

    constant_sym = {
        'skd' : Node,
        'start' : BoolSort() #to encode finiteness
    }
    relation_sym = {
        'on' : [Node],
        'd' : [Node], #to encode finiteness
    }
    function_sym = {
    }
    
    def axiom(sym):
        return True
    
    def init(sym):
        return And(
            ForAll(X,Not(sym['d'](X))),
            Not(sym['start']),
            ForAll(X,sym['on'](X))
        )
    
    param_add_to_d = {'n':Node}
    def add_to_d(sym1,sym2,param):
        return And(
            Not(sym1['start']),
            ForAll(X, sym2['d'](X)==Or(sym1['d'](X),X==param['n'])),
            ForAll(X, sym2['on'](X)==sym1['on'](X)),
            sym2['start']==sym1['start']
        )
    tr1 = ('tr1',param_add_to_d,add_to_d)
    
    param_start = {}
    def start(sym1,sym2,param):
        return And(
            Not(sym1['start']),
            ForAll(X,sym1['d'](X)), #once all nodes are in we can start
            sym2['start'],
            ForAll(X, sym2['on'](X)==sym1['on'](X)),
            ForAll(X, sym2['d'](X)==sym1['d'](X)),
        )
    tr2 = ('tr2',param_start,start)

    param_terminate = {}
    def terminate(sym1,sym2,param):
        return And(
            sym1['start'],
            sym2['start']==sym1['start'],
            ForAll(X, sym2['d'](X)==sym1['d'](X)),
            ForAll(X,sym2['on'](X)==And(sym1['on'](X),X!=sym1['skd']))
        )
    tr3 = ('tr1',param_terminate,terminate)

    ts = TS(sorts,axiom,init,[tr1,tr2,tr3],constant_sym,relation_sym,function_sym)

    #testing finiteness 
    #finite_constraint = FinitenessCondition(lambda sym,param: sym['d'](param['n']),{'n':Node},{})
    #print(finite_constraint.finiteness_check(ts))


    skd = z3.Const("skd", Node)
    on = z3.Function("on", Node, z3.BoolSort())
    start = z3.Bool("start")
    formula = foltl_nnf(z3.Not(z3.Implies(
        And(z3.ForAll(X, G(F(skd == X))),F(start)),
        F(z3.ForAll(X, z3.Not(on(X))))
    )))

    timer_system = timer_transition_system(formula, {"skd": skd})

    intersection = IntersectionTS(ts, timer_system)

    
    # pre = intersection.create_state("_pre")
    # pre_sym = pre.get_dict()
    # post = intersection.create_state("_post")
    # post_sym = post.get_dict()
    # print("---Axioms---")
    # print(intersection.axiom(pre_sym))
    # print(intersection.axiom(post_sym))
    # print("---Init---")
    # print(intersection.init(pre_sym))
    # print("---Transition---")
    # print(intersection.tr(pre_sym, post_sym))

    #The system rank is the number of on nodes
    param_n = {'n':Node}
    on =  lambda sym, param: sym['on'](param['n'])
    not_on = lambda sym, param: And(Not(sym['on'](param['n'])),sym['d'](param['n']))
    bin = BinaryFreeRank(on,param_n)
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
    timer_start = PositionInOrderFreeRank(
        lambda sym,param1,param2 : param1['x']<param2['x'],
        param_int,
        {'x':lambda sym,param:sym['t_<start>']}
    )
    all_skd_timers = ParPointwiseFreeRank(timer_for_on,param_n)
    
    conditional_timer = LinFreeRank(
        [all_skd_timers,timer_start],
        [lambda sym,param:sym['start'],lambda sym,param:Not(sym['start'])]
    )

    start_pred = lambda sym,param: Not(sym['start'])
    bin_start = BinaryFreeRank(start_pred)

    rank = LexFreeRank([number_of_on,bin_start,conditional_timer])

    timer_invariant = lambda sym: And(
        ForAll(X,sym['t_GF<skd == X>'](X)==0),
        #ForAll(X,sym['t_F<skd == X>'](X)==0), follows from previous
        sym['t_G<Exists(X, on(X))>']==0,
        #Exists(X,sym['on'](X)),
        Or(sym['start'],sym['t_<start>']>0),
    )
    system_invariant = lambda sym: And(
        Implies(sym['start'],ForAll(X,sym['d'](X))),
        Implies(Not(sym['start']),ForAll(X,sym['on'](X))),
    )
    invariant = lambda sym: And(timer_invariant(sym),system_invariant(sym))

    proof = TerminationProof(rank,invariant)
    proof.check_proof(intersection)
    #something is messy about the finiteness checks 
    #how do we verify that the number of 'on' nodes is finite? initially all nodes are on. 

trivial_termination_with_timers()
