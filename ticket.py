import z3
from z3 import *
from ts import *
from timers import *

def ticket():

    #Didnt check side conditions - might not hold

    Thread = DeclareSort('Thread')
    Ticket = DeclareSort('Ticket')
    X = Const('X',Ticket)
    Y = Const('Y',Ticket)
    Z = Const('Z',Ticket)
    K = Const('K',Ticket)
    K1 = Const('K1',Ticket)
    K2 = Const('K2',Ticket)
    M = Const('M',Ticket)
    T = Const('T',Thread)
    T1  = Const('T1',Thread)
    T2 = Const('T2',Thread)
    sorts = [Thread,Ticket]

    constant_sym = {
        'zero' : Ticket,
        'service' : Ticket,
        'next_ticket' : Ticket,
        'skolem_thread' : Thread #weird to have in signature
    }
    relation_sym = {
        'pc1' : [Thread],
        'pc2' : [Thread],
        'pc3' : [Thread],
        'm' : [Thread,Ticket],
        'le' : [Ticket,Ticket],
        'scheduled' : [Thread]
    }
    function_sym = {
    }
    
    def succ(sym,u,v):
        return And(
            sym['le'](u,v),
            Not(u==v),
            ForAll(X,Implies(sym['le'](u,X),Or(sym['le'](v,X),X==u)))
        )

    def order_le(sym):
        return And(
            #transitive, antisymmetric and total, with zero as minimal
            ForAll([X,Y,Z],Implies(And(sym['le'](X,Y),sym['le'](Y,Z)),sym['le'](X,Z))),
            ForAll([X,Y],Implies(And(sym['le'](X,Y),sym['le'](Y,X)),X==Y)),
            ForAll([X,Y],Or(sym['le'](X,Y),sym['le'](Y,X))),
            ForAll(X,sym['le'](sym['zero'],X)),
        )
    
    def scheduling(sym):
        #unclear if this is needed
        return ForAll([T1,T2],Implies(And(sym['scheduled'](T1),sym['scheduled'](T2)),T1==T2))

    def axiom(sym):
        return And(order_le(sym),
                   scheduling(sym))
    
    def init(sym):
        return And(
            ForAll(T,sym['pc1'](T)),
            ForAll(T,Not(sym['pc2'](T))),
            ForAll(T,Not(sym['pc3'](T))),
            sym['service']==sym['zero'],
            sym['next_ticket']==sym['zero'],
            ForAll([T,X],sym['m'](T,X)==(X==sym['zero'])),
            ForAll(T,Not(sym['scheduled'](T)))
        )
    
    immut = lambda sym1,sym2: And(
        sym2['zero']==sym1['zero'],
        ForAll([X,Y],sym2['le'](X,Y)==sym1['le'](X,Y)),
        sym2['skolem_thread']==sym1['skolem_thread']
    )
    
    param_step12 = {'t':Thread}
    def step12(sym1,sym2,param):
        t = param['t']
        return And(
            #guard
            sym1['scheduled'](t), #not sure this works
            sym1['pc1'](t),
            
            #updates
            immut(sym1,sym2),
            ForAll([T,X],sym2['m'](T,X)==If(
                T==t,
                X==sym1['next_ticket'],
                sym1['m'](T,X)
            )),
            ForAll(T,sym2['pc1'](T)==And(T!=t,sym1['pc1'](T))),
            ForAll(T,sym2['pc2'](T)==Or(T==t,sym1['pc2'](T))),
            ForAll(T,sym2['pc3'](T)==sym1['pc3'](T)),
            sym2['service']==sym1['service'],
            succ(sym1,sym1['next_ticket'],sym2['next_ticket'])
        )
    tr_step12 = ('step12',param_step12,step12)

    param_step22 = {'t':Thread,'k':Ticket}
    def step22(sym1,sym2,param):
        t = param['t']
        k = param['k']
        return And(
            #guard
            sym1['scheduled'](t), #not sure this works
            sym1['pc2'](t),
            sym1['m'](t,k),
            Not(sym1['le'](k,sym1['service'])),
            
            #updates
            immut(sym1,sym2),
            ForAll(T,sym2['pc1'](T)==sym1['pc1'](T)),
            ForAll(T,sym2['pc2'](T)==sym1['pc2'](T)),
            ForAll(T,sym2['pc3'](T)==sym1['pc3'](T)),
            ForAll([T,X],sym2['m'](T,X)==sym1['m'](T,X)),
            sym2['service']==sym1['service'],
            sym2['next_ticket']==sym1['next_ticket'],
        )
    tr_step22 = ('step22',param_step22,step22)

    param_step23 = {'t':Thread,'k':Ticket}
    def step23(sym1,sym2,param):
        t = param['t']
        k = param['k']
        return And(
            #guard
            sym1['scheduled'](t), #not sure this works
            sym1['pc2'](t),
            sym1['m'](t,k),
            sym1['le'](k,sym1['service']),
            
            #updates
            immut(sym1,sym2),
            ForAll(T,sym2['pc1'](T)==sym1['pc1'](T)),
            ForAll(T,sym2['pc2'](T)==And(T!=t,sym1['pc2'](T))),
            ForAll(T,sym2['pc3'](T)==Or(T==t,sym1['pc3'](T))),
            ForAll([T,X],sym2['m'](T,X)==sym1['m'](T,X)),
            sym2['service']==sym1['service'],
            sym2['next_ticket']==sym1['next_ticket'],
        )
    tr_step23 = ('step23',param_step23,step23)

    param_step31 = {'t':Thread}
    def step31(sym1,sym2,param):
        t = param['t']
        return And(
            #guard
            sym1['scheduled'](t), #not sure this works
            sym1['pc3'](t),
            
            #updates
            immut(sym1,sym2),
            ForAll(T,sym2['pc1'](T)==Or(T==t,sym1['pc1'](T))),
            ForAll(T,sym2['pc2'](T)==sym1['pc2'](T)),
            ForAll(T,sym2['pc3'](T)==And(T!=t,sym1['pc3'](T))),
            ForAll([T,X],sym2['m'](T,X)==sym1['m'](T,X)),
            succ(sym1,sym1['service'],sym2['service']),
            sym2['next_ticket']==sym1['next_ticket'],
        )
    tr_step31 = ('step31',param_step31,step31)

    transitions = [tr_step12,tr_step22,tr_step23,tr_step31]
    ts = TS(sorts,axiom,init,transitions,constant_sym,relation_sym,function_sym)

    scheduled = z3.Function("scheduled", Thread, z3.BoolSort())
    skolem_thread = z3.Const("skolem_thread", Thread)
    pc2 = z3.Function("pc2", Thread, z3.BoolSort())
    pc3 = z3.Function("pc3", Thread, z3.BoolSort())

    simplified_formula = foltl_nnf(
        And(
            ForAll(T,G(F(scheduled(T)))),
            F(And(pc2(skolem_thread),G(Not(pc3(skolem_thread)))))
        )
    )
    #non-negated property 
    formula = foltl_nnf(z3.Not(
        Implies(
            ForAll(T,G(F(scheduled(T)))),
            ForAll(T,G(Implies(pc2(T),F(pc3(T)))))
        )
    ))
    #user can write timer for Not(G(Implies(pc2(T),F(pc3(T))))

    #here we only give the def. of the skolem thread and not use it directly. 
    formula = foltl_nnf(z3.Not(
        Implies(
            Implies(Exists(T,F(And(pc2(T),G(Not(pc3(T)))))),
                F(And(pc2(skolem_thread),G(Not(pc3(skolem_thread))))),
            ),
            Implies(
            ForAll(T,G(F(scheduled(T)))),
            ForAll(T,G(Implies(pc2(T),F(pc3(T)))))
        ))
    ))

    timer_system = timer_transition_system(simplified_formula,{"skolem_thread":Thread})
    print(timer_system.constant_sym)
    intersection = IntersectionTS(ts, timer_system)

    #system invariant
    def system_invariant(sym):
        return And(
            ForAll(T,Or(sym['pc1'](T),sym['pc2'](T),sym['pc3'](T))),
            ForAll(T,Or(Not(sym['pc1'](T)),Not(sym['pc2'](T)))),
            ForAll(T,Or(Not(sym['pc1'](T)),Not(sym['pc3'](T)))),
            ForAll(T,Or(Not(sym['pc2'](T)),Not(sym['pc3'](T)))),
            ForAll([T,K1,K2],Implies(And(sym['m'](T,K1),sym['m'](T,K2)),K1==K2)),
            ForAll([T1,T2],Implies(And(sym['pc3'](T1),sym['pc3'](T2)),T1==T2)), #safety
            ForAll(T,Implies(sym['next_ticket']==sym['zero'],sym['m'](T,sym['zero']))),
            ForAll([T,M],Implies(And(sym['next_ticket']!=sym['zero'],sym['m'](T,M)),Not(sym['le'](sym['next_ticket'],M)))),
            ForAll(T,Implies(Or(sym['pc2'](T),sym['pc3'](T)),sym['next_ticket']!=sym['zero'])),
            ForAll([T1,T2,M],Implies(And(sym['m'](T1,M),sym['m'](T2,M),M!=sym['zero']),T1==T2)),
            ForAll([T,M],Implies(And(sym['pc2'](T),sym['m'](T,M)),sym['le'](sym['service'],M))),
            ForAll(T,Implies(sym['pc3'](T),sym['m'](T,sym['service']))),
            sym['le'](sym['service'],sym['next_ticket']),
            ForAll([T1,T2],Not(And(Not(sym['pc1'](T1)),Not(sym['pc1'](T2)),sym['m'](T1,sym['zero']),sym['m'](T2,sym['zero']),T1!=T2))),   
            ForAll([T,M],Implies(And(sym['pc1'](T),sym['m'](T,M),M!=sym['zero']),Not(sym['le'](sym['service'],M)))),
            ForAll(K,Implies(And(Not(sym['le'](sym['next_ticket'],K)),sym['le'](sym['service'],K)),Exists(T,And(sym['m'](T,K),Not(sym['pc1'](T)))))),
            Exists(M,sym['m'](sym['skolem_thread'],M)),
        )
    
    #timer invariant
    #you would be able to clean up the invariant if the timers had more precise semantics
    def timer_invariant(sym):
        return And(
            ForAll(T,sym['t_<G(F(scheduled(T)))>'](T)==0), # ForAll(T,G(F(scheduled(T)))
            Or(sym['t_<And(pc2(skolem_thread), G(Not(pc3(skolem_thread))))>']>=0, # F(And(...))
                And(sym['t_<G(Not(pc3(skolem_thread)))>']==0, # G(...)
                    sym['pc2'](sym['skolem_thread']), 
                    #sym['t_<pc2(skolem_thread)>']==0 #such an invariant doesn't hold without the better implementation of timers - equivalent to the one above
                    ForAll(K,Implies(sym['m'](sym['skolem_thread'],K),sym['le'](sym['service'],K)))
                )
            )
        )
    #maybe the user gives this as a temporal_invariant()
    
    
    invariant = lambda sym: And(system_invariant(sym),timer_invariant(sym))
    

    #system rank
    #difference in ticket between ticket of violating node? and service
    #something about position of nodes
    param_k = {'k':Ticket}
    between_service_and_skolem_ticket = lambda sym,param : And(
        sym['le'](sym['service'],param['k']),
        Exists(K,And(sym['m'](sym['skolem_thread'],K),sym['le'](param['k'],K)))
    )
    bin = BinaryFreeRank(between_service_and_skolem_ticket,param_k)
    diff_ticket_service = ParPointwiseFreeRank(bin,param_k)

    param_t = {'t':Thread}
    active = lambda sym,param: sym['m'](param['t'],sym['service'])
    not_active = lambda sym,param: Not(active(sym,param))
    not_pc3 = lambda sym,param: Not(sym['pc3'](param['t']))
    bin_not_pc3 = BinaryFreeRank(not_pc3,param_t)
    number_not_pc3 = ParPointwiseFreeRank(bin_not_pc3,param_t)

    system_rank = LexFreeRank([diff_ticket_service,number_not_pc3])

    #timer rank
    #timers of the scheduling of the node that holds the service
    #possibly something else small

    param_int = {'x':IntSort()}	
    scheduled_timer = PositionInOrderFreeRank(
        lambda sym,param1,param2 : param1['x']<param2['x'],
        param_int,
        {'x':lambda sym,param:sym['t_<scheduled(T)>'](param['t'])}
    )
    trivial_rank = BinaryFreeRank(lambda *args:True,param_t)
    timer_for_active = LinFreeRank(
        [scheduled_timer,trivial_rank],
        [active,not_active]
    )
    all_active_sched_timers = ParPointwiseFreeRank(timer_for_active,param_t)

    trigger_timer = PositionInOrderFreeRank(
        lambda sym,param1,param2 : param1['x']<param2['x'],
        param_int,
        {'x':lambda sym,param:sym['t_<And(pc2(skolem_thread), G(Not(pc3(skolem_thread))))>']}
    )

    after_trigger = lambda sym,param: And(sym['t_<G(Not(pc3(skolem_thread)))>']==0,sym['pc2'](sym['skolem_thread']))
    before_trigger = lambda sym,param: Not(after_trigger(sym,param))
    
    system_and_scheduling_rank = LexFreeRank(
        [system_rank,all_active_sched_timers],
    )

    rank = LinFreeRank(
        [trigger_timer,system_and_scheduling_rank],
        [before_trigger,after_trigger]
    )
    
    proof = TerminationProof(rank,invariant)
    proof.check_proof(intersection)
    

ticket()