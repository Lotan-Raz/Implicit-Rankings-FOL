import z3
from z3 import *
from ts import *
from timers import *

def ticket():

    #NOT TESTED

    Thread = DeclareSort('Thread')
    Ticket = DeclareSort('Ticket')
    X = Const('X',Ticket)
    Y = Const('Y',Ticket)
    Z = Const('Z',Ticket)
    T = Const('T',Thread)
    S = Const('S',Thread)  
    sorts = [Thread,Ticket]

    constant_sym = {
        'zero' : Ticket,
        'service' : Ticket,
        'next_ticket' : Ticket
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
        return

    def order_le(sym):
        return And(
            #transitive, antisymmetric and total, with zero as minimal
            ForAll([X,Y,Z],Implies(And(sym['le'](X,Y),sym['le'](Y,Z)),sym['le'](X,Z))),
            ForAll([X,Y],Implies(And(sym['le'](X,Y),sym['le'](Y,X)),X==Y)),
            ForAll([X,Y],Or(sym['le'](X,Y),sym['le'](Y,X))),
            ForAll(X,sym['le'](sym['zero'],X)),
        )

    def axiom(sym):
        return And(order_le(sym))
    
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
        ForAll([X,Y],sym2['le'](X,Y)==sym1['le'](X,Y))
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
    tr_step12 = ('step12',step12,param_step12)

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
    tr_step22 = ('step22',step22,param_step22)

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
    tr_step23 = ('step23',step23,param_step23)

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
    tr_step31 = ('step31',step31,param_step31)

    transitions = [tr_step12,tr_step22,tr_step23,tr_step31]
    ts = TS(sorts,axiom,init,transitions,constant_sym,relation_sym,function_sym)

    scheduled = z3.Function("scheduled", Thread, z3.BoolSort())
    pc2 = z3.Function("pc2", Thread, z3.BoolSort())
    pc3 = z3.Function("pc3", Thread, z3.BoolSort())
    formula = foltl_nnf(z3.Not(
        Implies(
            ForAll(T,G(F(scheduled(T)))),
            ForAll(T,G(Implies(pc2(T),F(pc3(T)))))
        )
    ))

    timer_system = timer_transition_system(formula,{})
    intersection = IntersectionTS(ts, timer_system)

    #NOT TESTED


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


ticket()