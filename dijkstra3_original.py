from z3 import *
from ts import *

def dijsktra3():

    #Relevant papers: A belated proof of self-stabilization, An exercise in proving self-stabilization with a variant function.

    print('dijkstra3')

    Node = DeclareSort('Node')
    Value, (zero, one, two) = EnumSort('Value',('zero','one','two'))
    sorts = [Node]

    def plus1mod3(x):
        return If(x==zero,one,
                  If(x==one,two,
                     zero))
    def plus2mod3(x):
        return If(x==zero,two,
                  If(x==one,zero,
                     one))
    
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)

    constant_sym = { 'skd' : Node,
                     'top' : Node,
                     'bot' : Node,
                     'node_h' : Node,
                     }
    relation_sym = {'leq_node' : [Node,Node],
    }
    function_sym = {'next' : [Node,Node],
                    'prev' : [Node,Node],
                    'a' : [Node,Value] }
    
    def init(sym):
        return BoolVal(True)

    def succ_node(sym,u,v):
        return Or(
        ForAll(W,And(sym['leq_node'](v,W),sym['leq_node'](W,u))),
        And(u!=v,
            sym['leq_node'](u,v),
            ForAll(W,Or(sym['leq_node'](v,W),sym['leq_node'](W,u))))
        )

    def axiom_leq_node(sym):
        return ForAll([X,Y,Z],And(
        Implies(And(sym['leq_node'](X,Y),sym['leq_node'](Y,Z)),sym['leq_node'](X,Z)),
        Implies(And(sym['leq_node'](X,Y),sym['leq_node'](Y,X)),X==Y),
        Or(sym['leq_node'](X,Y),sym['leq_node'](Y,X)),
        sym['leq_node'](sym['bot'],X),
        sym['leq_node'](X,sym['top']),
        succ_node(sym,sym['prev'](X),X),
        succ_node(sym,X,sym['next'](X)),
        ))

    def induction_axiom(sym):
        return Implies(
            Exists(Y,sym['a'](Y)!=sym['a'](sym['bot'])),
            Exists(Z,And(sym['a'](Z)!=sym['a'](sym['bot']),ForAll(Y,Implies(sym['a'](Y)!=sym['a'](sym['bot']),sym['leq_node'](Z,Y)))))
        )
        
    def axiom(sym):
        return And(axiom_leq_node(sym),
                   induction_axiom(sym),
                   ) 

    def priv_bot(sym,i):
        return plus1mod3(sym['a'](i))==sym['a'](sym['next'](i))
    
    def move_bot(sym1,sym2,i): 
        return And(
            plus2mod3(sym1['a'](i))==sym2['a'](i),
            ForAll(X,Implies(X!=i,sym2['a'](X)==sym1['a'](X)))
        )

    def priv_normal(sym,i):
        local_plus1 = plus1mod3(sym['a'](i))
        return Or(sym['a'](sym['prev'](i))==local_plus1,sym['a'](sym['next'](i))==local_plus1)
    
    def move_normal(sym1,sym2,i):
        return And(
            plus1mod3(sym1['a'](i))==sym2['a'](i),
            ForAll(X,Implies(X!=i,sym2['a'](X)==sym1['a'](X)))
        )
    
    def priv_top(sym,i):
        return And(
            sym['a'](sym['prev'](i))==sym['a'](sym['bot']),
            sym['a'](i)!=plus1mod3(sym['a'](sym['bot'])),
        )
    
    def move_top(sym1,sym2,i):
        return And(
            plus1mod3(sym1['a'](sym1['bot']))==sym2['a'](i),
            ForAll(X,Implies(X!=i,sym2['a'](X)==sym1['a'](X)))
        )
    
    def priv(sym,i):
        return Or(
            And(i==sym['bot'],priv_bot(sym,i)),
            And(i==sym['top'],priv_top(sym,i)),
            And(i!=sym['bot'],i!=sym['top'],priv_normal(sym,i)),
        )
    
    def move(sym1,sym2,i):
        return Or(
            And(i==sym1['bot'],move_bot(sym1,sym2,i)),
            And(i==sym1['top'],move_top(sym1,sym2,i)),
            And(i!=sym1['bot'],i!=sym1['top'],move_normal(sym1,sym2,i)),
        )

    def move_idle(sym1,sym2,i):
        return ForAll(X,sym2['a'](X)==sym1['a'](X))

    param_wakeup = {'n' : Node}
    def tr_wakeup(sym1,sym2,param):
        return And(
        sym2['skd']==param['n'],
        sym2['top']==sym1['top'],
        sym2['bot']==sym1['bot'],
        sym2['node_h']==sym1['node_h'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll(X,sym2['next'](X)==sym1['next'](X)),
        ForAll(X,sym2['prev'](X)==sym1['prev'](X)),
        If(priv(sym1,param['n']),
           move(sym1,sym2,param['n']),
           move_idle(sym1,sym2,param['n'])
           )    
        )
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)
    #ts.bounded_check([true,true])

    def no_deadlock(sym):
        return Exists(X,priv(sym,X))
    
    #ts.check_inductiveness(no_deadlock) #works with ind. axiom

    def stable(sym):
        return And(
            ForAll([X,Y],Implies(And(priv(sym,X),priv(sym,Y)),X==Y)),
        )
    
    def stable_no_dead(sym):
        return And(
            no_deadlock(sym),
            stable(sym)
        )
    
    #ts.check_tr_maintains_inv(stable_no_dead) #takes a super long time    

    #probably we can find something more general that suffices for both of these::

    def case10_axiom(sym):
        return Implies(
            And(plus1mod3(sym['a'](sym['top']))==sym['a'](sym['bot']),
                plus1mod3(sym['a'](sym['top']))==sym['a'](sym['prev'](sym['top']))),
            Or(stable(sym),
               Exists(X,And(
                   X!=sym['top'],
                   Not(succ_node(sym,X,sym['top'])),
                   sym['a'](X)!=sym['a'](sym['next'](X))
                   )))
        )

    def stability_axiom(sym):
        return Implies(
            And(stable(sym),priv(sym,sym['bot'])),
            ForAll(X,Implies(And(X!=sym['bot'],X!=sym['top'],sym['prev'](X)!=sym['bot']),And(sym['a'](X)==sym['a'](sym['prev'](X))))),
            ForAll(X,Implies(And(X!=sym['bot'],X!=sym['top'],sym['next'](X)!=sym['top']),And(sym['a'](X)==sym['a'](sym['next'](X)))))
        )
    
    ts.check_inductiveness(stability_axiom)

    
dijsktra3()