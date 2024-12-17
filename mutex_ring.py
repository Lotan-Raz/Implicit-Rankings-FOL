from z3 import *
from ts import *

def mutex_ring():
    
    #Classic mutex in a ring - a token moves around a ring, allowing the holder to enter the critical section
    #taken from Fang, Y., Piterman, N., Pnueli, A. and Zuck, L., 2004, January.
    #Liveness with invisible ranking. 
    #In International Workshop on Verification, Model Checking, and Abstract Interpretation (pp. 223-238). Berlin, Heidelberg: Springer Berlin Heidelberg.

    print('mutex_ring')

    Loc, (waiting,critical,neutral) = EnumSort('Loc',('waiting','critical','neutral'))

    true = lambda sym: True 

    Node = DeclareSort('Node')
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    sorts = [Node]

    constant_sym = {
        'epsilon_token' : Node,
        'skd' : Node,
        'leader' : Node,
        'node_her1' : Node,
    }
    relation_sym = {
        'btw' : [Node,Node,Node],
        'token' : [Node]
    }
    function_sym = {
        'node_loc' : [Node,Loc]
    }

    axiom = lambda sym: And(
        ForAll([X,Y,Z,W],Implies(And(sym['btw'](W,X,Y),sym['btw'](W,Y,Z)),sym['btw'](W,X,Z))),
        ForAll([W,X,Y],Implies(sym['btw'](W,X,Y),Not(sym['btw'](W,Y,X)))),
        ForAll([W,X,Y],Or(sym['btw'](W,X,Y),sym['btw'](W,Y,X),W==X,W==Y,X==Y)),
        ForAll([X,Y,Z],Implies(sym['btw'](X,Y,Z),sym['btw'](Y,Z,X))),
        Implies(Exists(X,sym['token'](X)),sym['token'](sym['epsilon_token']))
    )
    init = lambda sym: And(
        ForAll(X,sym['token'](X) == (X == sym['leader'])),
        ForAll(X,sym['node_loc'](X) == neutral)
    )

    param_wakeup = {'n': Node,'succ': Node}
    tr_wakeup = lambda sym1,sym2,param: And(
        sym1['skd']==param['n'],
        param['n'] != param['succ'],
        ForAll(Z,Or(sym1['btw'](param['n'],param['succ'],Z),Z==param['n'],Z==param['succ'])),
        sym2['node_her1']==sym1['node_her1'],
        sym2['leader']==sym1['leader'],
        ForAll([X,Y,Z],sym2['btw'](X,Y,Z)==sym1['btw'](X,Y,Z)),
        If(sym1['token'](param['n']),
           If(sym1['node_loc'](param['n'])==neutral,
              ForAll(X,And(
                sym2['token'](X)==Or(And(sym1['token'](X),X!=param['n']),X==param['succ']),
                sym2['node_loc'](X)==sym1['node_loc'](X))),
              If(sym1['node_loc'](param['n'])==waiting,
                ForAll(X,And(
                sym2['token'](X)==sym1['token'](X),
                sym2['node_loc'](X)==If(X==param['n'],critical,sym1['node_loc'](X)))),
                ForAll(X,And(  #else loc = critical 
                sym2['token'](X)==sym1['token'](X),
                sym2['node_loc'](X)==If(X==param['n'],neutral,sym1['node_loc'](X)))))
              ),
        And(ForAll(X,sym2['token'](X)==sym1['token'](X)),
            If(sym1['node_loc'](param['n'])==neutral,
               ForAll(X,sym2['node_loc'](X)==If(X==param['n'],
                                                 waiting,
                                                 sym1['node_loc'](X))),
               ForAll(X,sym2['node_loc'](X)==sym1['node_loc'](X)))))
    )
    tr1 = ['send',param_wakeup,tr_wakeup]

    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)
    inv = lambda sym: ForAll([X,Y],Implies(And(sym['token'](X),sym['token'](Y)),X==Y))
    #ts.check_inductiveness(inv)
    #ts.bounded_check([true,true,true,true,lambda sym: Exists([X,Y],And(sym['node_loc'](X)==critical,sym['btw'](sym['leader'],Y,X)))])

    r = lambda sym,param : param['n'] == sym['skd']
    sort_dict = {'n' : Node}
    p = lambda sym: sym['node_loc'](sym['node_her1'])==waiting
    q = lambda sym: sym['node_loc'](sym['node_her1'])==critical
    prop = LivenessProperty(p,q,[r],[sort_dict])

    n_node = {'n':Node}
    pred_token = lambda sym,param: sym['token'](param['n'])
    pred_waiting_token = lambda sym,param: And(sym['node_loc'](param['n'])==waiting,sym['token'](param['n']))
    delta0_free = BinaryFreeRank(pred_waiting_token,n_node)
    pred_critical_token = lambda sym,param: And(sym['node_loc'](param['n'])==critical,sym['token'](param['n']))
    delta1_free = BinaryFreeRank(pred_critical_token,n_node)
    pred_neutral_token = lambda sym,param: And(sym['node_loc'](param['n'])==neutral,sym['token'](param['n']))
    delta2_free = BinaryFreeRank(pred_neutral_token,n_node)
    delta_free = LexFreeRank([delta0_free,delta1_free,delta2_free],n_node)

    less_btw_her_first = lambda sym,param1,param2: Or(sym['btw'](sym['node_her1'],param1['n'],param2['n']),And(param1['n']==sym['node_her1'],param2['n']!=sym['node_her1'])) 
    less_btw_her_last = lambda sym,param1,param2: Or(sym['btw'](sym['node_her1'],param1['n'],param2['n']),And(param2['n']==sym['node_her1'],param1['n']!=sym['node_her1'])) 

    ##first rank - as described in section 6
    rank_lex = ParLexFreeRank(delta_free,n_node,less_btw_her_last,{})

    rank_lex.print_reduced(ts)

    ##second rank - as described in appendix B
    #somehow more intuitive but requires all these hints, so overall worse
    hint1 = lambda sym1,sym2,param1,param2: sym1['epsilon_token']
    hint2 = lambda sym1,sym2,param1,param2: sym2['epsilon_token']
    hint_skd = lambda sym1,sym2,param1,param2 : sym1['skd']
    
    hint1x = {'n':hint1}
    hint2x = {'n':hint2}
    hint_skdx = {'n' : hint_skd}
    hints = [hint1x,hint2x]
    
    less_btw_her_last_reversed = lambda sym,param1,param2 : less_btw_her_last(sym,param2,param1)

    con = lambda sym,param_quant,param_free: sym['token'](param_quant['n'])
    rank_lin = ParLinFreeRank(delta_free,n_node,con,less_btw_her_last_reversed,{},
                          [hint1x],hints)

    rho = lambda sym: And(Exists(X,sym['token'](X)),
                             inv(sym) #safety invariant - needed for proof with rank_lin
                             )
    phi = lambda sym: And(rho(sym),
                          p(sym),
                          Not(q(sym))) 
    psi = lambda sym,param: sym['token'](param['n'])

    proof = LivenessProof(prop,rank_lin,rho,phi,[psi])

    import time
    start_time = time.time()
    proof.check_proof(ts)
    end_time = time.time()
    print(end_time-start_time)

mutex_ring()
