from z3 import *
from ts import *

def dijsktra2():

    print('dijkstra2')

    Node = DeclareSort('Node')
    sorts = [Node]

    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)

    constant_sym = { 'skd' : Node,
                     'top' : Node,
                     'bot' : Node,
                     'node_h' : Node
                     }
    relation_sym = {'leq_node' : [Node,Node],
                    'x' : [Node],
                    'up' : [Node]               
    }
    function_sym = {'next' : [Node,Node],
                    'prev' : [Node,Node], }
    
    def init(sym):
        return And(
            sym['up'](sym['bot'])==True,
            sym['up'](sym['top'])==False,
        )

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
            Exists(Y,sym['up'](Y)==False),
            Exists(Z,And(sym['up'](Z)==False,ForAll(Y,Implies(sym['up'](Y)==False,sym['leq_node'](Z,Y)))))
        )

    def axiom(sym):
        return And(axiom_leq_node(sym),
                   induction_axiom(sym)) 

    def priv_below(sym,i):
        return And(sym['x'](i) != sym['x'](sym['prev'](i)),i!=sym['bot'])

    def move_below_normal(sym1,sym2,i):
        return And(
            sym2['x'](i)==Not(sym1['x'](i)),
            sym2['up'](i)==True,
            ForAll(X,Implies(X!=i,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=i,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_below_top(sym1,sym2,i):
        return And(
            sym2['x'](i)==Not(sym1['x'](i)),
            sym2['up'](i)==sym1['up'](i),
            ForAll(X,Implies(X!=i,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=i,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_below(sym1,sym2,i):
        return If(i==sym1['top'],
            move_below_top(sym1,sym2,i),
            move_below_normal(sym1,sym2,i))
            
    def priv_above(sym,i):
        return And(sym['x'](i)==sym['x'](sym['next'](i)),sym['up'](i),Not(sym['up'](sym['next'](i))),i!=sym['top'])
    
    def move_above_normal(sym1,sym2,i):
        return And(
            sym2['x'](i)==sym1['x'](i),
            sym2['up'](i)==False,
            ForAll(X,Implies(X!=i,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=i,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_above_bot(sym1,sym2,i):
        return And(
            sym2['x'](i)==Not(sym1['x'](i)),
            sym2['up'](i)==sym1['up'](i),
            ForAll(X,Implies(X!=i,sym2['x'](X)==sym1['x'](X))),
            ForAll(X,Implies(X!=i,sym2['up'](X)==sym1['up'](X))),
        )
    
    def move_above(sym1,sym2,i):
        return If(i==sym1['bot'],
            move_above_bot(sym1,sym2,i),
            move_above_normal(sym1,sym2,i))
    
    def any_priv(sym,i):
        return Or(priv_above(sym,i),priv_below(sym,i))

    def move_idle(sym1,sym2,i):
        return And(
            ForAll(X,sym2['x'](X)==sym1['x'](X)),
            ForAll(X,sym2['up'](X)==sym1['up'](X)),
        ) 

    param_wakeup = {'n' : Node}
    def tr_wakeup(sym1,sym2,param):
        return And(
        sym1['skd']==param['n'],
        sym2['top']==sym1['top'],
        sym2['bot']==sym1['bot'],
        sym2['node_h']==sym1['node_h'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll(X,sym2['next'](X)==sym1['next'](X)),
        ForAll(X,sym2['prev'](X)==sym1['prev'](X)),
        Or(
            And(priv_above(sym1,param['n']),move_above(sym1,sym2,param['n'])),
            And(priv_below(sym1,param['n']),move_below(sym1,sym2,param['n'])),
            And(Not(any_priv(sym1,param['n'])),move_idle(sym1,sym2,param['n'])),
        ))
    
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    def no_deadlock(sym):
        return Exists(X,any_priv(sym,X))

    def inv(sym):
        return And(no_deadlock(sym),init(sym))

    #ts.bounded_check([true,true])
    #ts.check_inductiveness(inv)

    def stable(sym):
        return ForAll([X,Y],And(
            Implies(And(any_priv(sym,X),any_priv(sym,Y)),X==Y),
            Not(And(priv_above(sym,X),priv_below(sym,X)))
        ))

    def inv_stable(sym):
        return And(stable(sym),init(sym))


    #Simpler Liveness Property - after stable has been reached
    #Two properties:
    #Property1 stable -> forall n. G ( n != bot -> F priv_below(n))
    ts1 = TS(sorts,axiom,inv_stable,[tr1],constant_sym,relation_sym,function_sym)

    r = lambda sym,param: Implies(Exists(X,any_priv(sym,X)),any_priv(sym,sym['skd']))
    sort_dict = {}
    p1 = lambda sym: sym['node_h']!=sym['bot']
    q1 = lambda sym: priv_below(sym,sym['node_h'])
    prop1 = LivenessProperty(p1,q1,[r],[sort_dict])

    rho = inv
    phi1 = lambda sym: And(
        p1(sym),rho(sym),Not(q1(sym))
    )
    psi = lambda sym,param: BoolVal(True)

    strict_order = lambda sym,param1,param2 : And(sym['leq_node'](param1['i'],param2['i']),param1['i']!=param2['i'])
    reverse_order = lambda sym,param1,param2 : And(sym['leq_node'](param2['i'],param1['i']),param1['i']!=param2['i'])

    after_h = lambda sym,param : And(priv_below(sym,param['i']),sym['leq_node'](sym['node_h'],param['i']))
    before_h = lambda sym,param : And(priv_below(sym,param['i']),sym['leq_node'](param['i'],sym['node_h']))
    priv_above_pred = lambda sym,param: priv_above(sym,param['i'])


    #Doesnt work, should just try to prove these on the abstraction and not here
    

    delta10 = BinaryFreeRank(after_h,{'i':Node})
    delta11 = BinaryFreeRank(priv_above_pred,{'i':Node})
    delta12 = BinaryFreeRank(before_h,{'i':Node})
    
    delta13 = ParLexFreeRank(delta10,{'i':Node},strict_order)
    delta14 = ParLexFreeRank(delta11,{'i':Node},reverse_order)
    delta15 = ParLexFreeRank(delta12,{'i':Node},strict_order)

    delta1 = LexFreeRank([delta13,delta14,delta15])
    
    proof1 = LivenessProof(prop1,delta1,rho,phi1,[psi])

    print('checking proof 1') ; proof1.check_proof(ts1)





    #Simpler ranking function (?): with a direct sum:
    delta_below = BinaryRankingFunction(priv_below)
    delta_above = BinaryRankingFunction(priv_above)
    
    delta_comp1 = OrderLexicographicRank(delta_below,Node,strict_order)
    delta_comp2 = OrderLexicographicRank(delta_above,Node,reverse_order)
    delta_comp3 = OrderLexicographicRank(delta_below,Node,strict_order)

    cond1 = lambda sym: Exists(X,And(sym['leq_node'](sym['node_h'],X),priv_below(sym,X)))
    cond2 = lambda sym: Exists(X,priv_above(sym,X))
    cond3 = lambda sym: Exists(X,And(sym['leq_node'](X,sym['node_h']),priv_below(sym,X)))

    delta_sum = DirectSumRank([delta_comp1,delta_comp2,delta_comp3],[cond1,cond2,cond3])
    delta_sum.print_reduced(ts)

    proof_sum = ParamLivenessProof(prop1,delta_sum,rho1,phi1,[psi1])

    print('checking proof with directsum') ; proof_sum.check_proof(ts1)

    #Property forall n. G (n != bot -> F priv_above(n))
    #Would be proved similarly

dijsktra2()
