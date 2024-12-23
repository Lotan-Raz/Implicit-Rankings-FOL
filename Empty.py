from z3 import *
from ts import *

def name():
    
    #This file shows an example of how to use our implementation:
    #specifying signature, system, liveness property and proof
    #The example shown here is completely meaningless, just an example of the syntax.

    #specifying signature:
    Node = DeclareSort('Node')
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    sorts = [Node]

    constant_sym = {
        'a' : Node,
        'b' : Node,
        'c' : Node,
    }
    relation_sym = {
        'on' : [Node],
        'msg' : [Node,Node],
        'flag' : []
    }
    function_sym = {
        'f' : [Node,Node]
    }
    
    #background axioms (assumed on all states)
    def axiom(sym):
        return True
    
    #initial condition:
    def init(sym):
        return True
    
    #specifying transitions: transition parameters are existentially quantified
    param_trans1 = {'n': Node}
    def trans1(sym1,sym2,param):
        return And(
            ForAll(X,sym2['on'](X)==sym1['on'](X))
        )
    tr1 = ('tr1',param_trans1,trans1)

    #specifying a transition system:
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    #bounded model checking
    ts.bounded_check([true,true]) 

    #specifying and checking invariants - good if you also want to prove some safety properties.
    def inv(sym):
        return True
    
    ts.check_inductiveness(inv)

    #specifying liveness properties
    r1 = lambda sym,param: sym['flag']()
    param_r1 = {}
    r2 = lambda sym,param: sym['msg'](param['x'],param['y'])
    param_r2 = {'x':Node,'y':Node}
    p = true 
    q = lambda sym: Or(sym['flag'](),ForAll([X,Y],Not(sym['msg'](X,Y))))
    
    #example liveness property with multiple fairness constraints
    prop = LivenessProperty(p,q,[r1,r2],[param_r1,param_r2])

    #liveness proof
    rho = inv 
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = true

    predicate = lambda sym,param: sym['msg'](sym['a'],sym['b'])
    binary_rank = BinaryFreeRank(predicate,{})

    proof = LivenessProof(prop,binary_rank,rho,phi,[psi])
    proof.check_proof(ts)


name()