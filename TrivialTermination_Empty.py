from z3 import *
from ts import *

def name():
    
    #This file presents the 'trivial termination' protocol where a network is comprised of a finite number of machines
    #The code for each machine is to terminate when it is scheduled for the first time
    #we want to show that under fair scheduling eventually all machines are terminated.
    #This is a simple exercise to show reusability.

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
    
    r1 = lambda sym,param: sym['skd']==param['n']
    param_r1 = {'n':Node}
    p = true 
    q = lambda sym: ForAll(X,Not(sym['on'](X)))
    
    prop = LivenessProperty(p,q,[r1],[param_r1])

    rho = true
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = lambda sym,param: sym['on'](param['n'])

    ##You need to find appropriate rank using the constructors 
    rank = BinaryFreeRank(true) #trivial ranking that doesn't prove anything
    
    proof = LivenessProof(prop,rank,rho,phi,[psi])
    proof.check_proof(ts)


name()