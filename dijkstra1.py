
from z3 import *
from ts import *

def dijsktra():

    print('dijkstra')

    Node = DeclareSort('Node')
    Value = DeclareSort('Value')
    sorts = [Node,Value]

    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    S = Const('S',Value)
    T = Const('T',Value)
    R = Const('R',Value)
    U = Const('U',Value)
    V = Const('V',Value)

    constant_sym = { 'skd' : Node,
                     'bot' : Node,
                     'witness_value' : Value,
                     'node_h' : Node,
                     }
    relation_sym = {'leq_node' : [Node,Node],
                    'leq_value' : [Value,Value]}
    function_sym = { 'a' : [Node,Value],
                     #'next' : [Node,Node], not using it
                      'prev' : [Node,Node], }
    
    two_nodes = lambda sym: Exists([X,Y],And(X!=Y,ForAll(W,Or(X==W,Y==W))))
    three_values = lambda sym: Exists([S,T,R],And(
        S!=T,S!=R,T!=R,
        ForAll(V,Or(V==S,V==R,V==T))
    ))
    three_nodes = lambda sym: Exists([X,Y,Z],And(X!=Y,Y!=Z,X!=Z,ForAll(W,Or(X==W,Y==W,Z==W))))
    four_values = lambda sym: Exists([S,T,R,U],And(
        S!=T,S!=R,S!=U,T!=R,T!=U,R!=U,
        ForAll(V,Or(V==S,V==R,V==T,V==U))
    ))
    small_model = lambda sym: And(three_nodes(sym),four_values(sym))

    succ_node = lambda sym,u,v : Or(
        ForAll(W,And(sym['leq_node'](v,W),sym['leq_node'](W,u))),
        And(u!=v,
            sym['leq_node'](u,v),
            ForAll(W,Or(sym['leq_node'](v,W),sym['leq_node'](W,u))))
    )
    btw = lambda sym,v1,v2,v3 : And(
        v1!=v2,v2!=v3,v3!=v1,
        Or(
            And(sym['leq_value'](v1,v2),sym['leq_value'](v2,v3)),
            And(sym['leq_value'](v1,v2),sym['leq_value'](v3,v1)),
            And(sym['leq_value'](v2,v3),sym['leq_value'](v3,v1))
        )
    )
    succ_value = lambda sym,u,v : Or(
        ForAll(U,And(sym['leq_value'](v,U),sym['leq_value'](U,u))),
        And(u!=v,
            sym['leq_value'](u,v),
            ForAll(U,Or(sym['leq_value'](v,U),sym['leq_value'](U,u))))
    )
    priv = lambda sym,i : Or(
        And(i == sym['bot'], sym['a'](i) == sym['a'](sym['prev'](i))),
        And(i != sym['bot'], sym['a'](i) != sym['a'](sym['prev'](i)))
    )

    axiom_leq_node = lambda sym: ForAll([X,Y,Z],And(
        Implies(And(sym['leq_node'](X,Y),sym['leq_node'](Y,Z)),sym['leq_node'](X,Z)),
        Implies(And(sym['leq_node'](X,Y),sym['leq_node'](Y,X)),X==Y),
        Or(sym['leq_node'](X,Y),sym['leq_node'](Y,X)),
        sym['leq_node'](sym['bot'],X),
        succ_node(sym,sym['prev'](X),X),
        #succ_node(sym,X,sym['next'](X)),
    ))
    axiom_leq_value = lambda sym: ForAll([S,T,R],And(
        Implies(And(sym['leq_value'](S,R),sym['leq_value'](R,T)),sym['leq_value'](S,T)),
        Implies(And(sym['leq_value'](S,R),sym['leq_value'](R,S)),S==R),
        Or(sym['leq_value'](S,R),sym['leq_value'](R,S)),
    ))
    axiom_well_founded = lambda sym: Implies(
        Exists(X,sym['a'](X)!=sym['a'](sym['bot'])),
        Exists(X,And(
            sym['a'](X)!=sym['a'](sym['bot']),
            ForAll(Y,Implies(sym['a'](Y)!=sym['a'](sym['bot']),sym['leq_node'](X,Y)))))
    )#this well-foundedness axiom is not legal in ivy/mypyvy, adding it is sound for finite models - this is neta's work.
    
    #if we have more values than keys then there is a value not present in the ring
    axiom_more_values_keys = lambda sym: Exists(R,ForAll(X,sym['a'](X)!=R))

    #defining 'witness value' as epsilon(minimal missing value in ring)
    witness_def = lambda sym: Implies(
        Exists(R,ForAll(X,sym['a'](X)!=R)),
        And(
            ForAll(X,sym['a'](X)!=sym['witness_value']),
            ForAll(S,Implies(ForAll(X,sym['a'](X)!=S),Or(
                S==sym['witness_value'],
                btw(sym,sym['a'](sym['bot']),sym['witness_value'],S))))))
   
    #witness_def = lambda sym: Implies(
    #    Exists(R,ForAll(X,sym['a'](X)!=R)),
    #    ForAll(X,sym['a'](X)!=sym['witness_value']) ) 

    axiom = lambda sym : And(
        axiom_leq_node(sym),
        axiom_leq_value(sym),
        axiom_well_founded(sym),
        axiom_more_values_keys(sym), 
        witness_def(sym),
        #small_model(sym)
    ) 

    init = lambda sym: True 

    param_wakeup = {'n' : Node}
    tr_wakeup = lambda sym1,sym2,param: And(
        sym1['skd']==param['n'],
        
        sym2['bot']==sym1['bot'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll([S,T],sym2['leq_value'](S,T)==sym1['leq_value'](S,T)),
        ForAll(X,sym2['prev'](X)==sym1['prev'](X)),
        sym2['node_h']==sym1['node_h'],

        If(priv(sym1,param['n']),
           If(param['n']==sym1['bot'],And(
            succ_value(sym1,sym1['a'](sym1['prev'](param['n'])),sym2['a'](param['n'])), 
            ForAll(X,Implies(X!=param['n'],
                             sym2['a'](X)==sym1['a'](X)))
           ),
           And(
            sym2['a'](param['n'])==sym1['a'](sym1['prev'](param['n'])),
            ForAll(X,Implies(X!=param['n'],
                             sym2['a'](X)==sym1['a'](X)))
           )),
            ForAll(X,sym2['a'](X)==sym1['a'](X))
           )
    )
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    #ts.bounded_check([true,true]) #important for checking system is not null
    exists_privilege = lambda sym: Exists(X,priv(sym,X))
    #ts.check_inductiveness(exists_privilege) 

    #As a first attempt we consider breaking the proof into 4 lemmas:    
    #P1 : under fair scheduling globally eventually node 'bot' is privileged and scheduled
    #P2 : if infinitely often 'bot' is privileged and scheduled eventually 'bot' holds a unique value in the ring
    #P3 : starting in a state where 'bot' holds a unique value eventually only 'bot' will be privileged
    #P4 : starting in a state where only 'bot' is privledged globally there is a unique privilege in the ring.

    n_dict = {'n':Node}

    #P1 : as long as a privileged node is eventually scheduled eventually special will be scheduled
    r1 = lambda sym,param : Implies(Exists(X,priv(sym,X)),priv(sym,sym['skd']))
    p1 = lambda sym: True
    q1 = lambda sym: And(priv(sym,sym['bot']),sym['skd']==sym['bot'])
    prop1 = LivenessProperty(p1,q1,[r1],[n_dict])

    rho1 = lambda sym: And(exists_privilege(sym))
    phi1 = lambda sym: And(rho1(sym),Not(q1(sym)))
    psi1 = lambda sym,param: True
    
    order_bot_first = lambda sym,param1,param2 : And( sym['leq_node'](param1['n'],param2['n']) , param1['n']!=param2['n'] )
    order_bot_last = lambda sym,param1,param2: And(param1['n']!=param2['n'],Or(And(sym['leq_node'](param1['n'],param2['n']),param1['n']!=sym['bot']),param2['n']==sym['bot']))

    pred_priv_n = lambda sym,param : priv(sym,param['n'])
    binary_priv_n = BinaryFreeRank(pred_priv_n,n_dict)
    rank_agg_lex = ParLexFreeRank(binary_priv_n,n_dict,order_bot_last)
    
    rank1 = rank_agg_lex
    proof1 = LivenessProof(prop1,rank1,rho1,phi1,[psi1])
    print("checking P1") ; proof1.check_proof(ts) 

    #P2 : if infinitely often 'bot' is privileged and scheduled eventually 'bot' holds a unique value in the ring

    r2 = lambda sym,param: And(priv(sym,sym['bot']),sym['skd']==sym['bot'])
    p2 = lambda sym: True
    q2 = lambda sym: ForAll(X,Implies(X!=sym['bot'],
                                      sym['a'](X)!=sym['a'](sym['bot'])))
    prop2 = LivenessProperty(p2,q2,[r2],[{}])
    
    rho2 = lambda sym: True
    phi2 = lambda sym: And(rho2(sym))
    psi2 = lambda sym,param: True
    
    v_value = {'v':Value}
    counted = lambda sym,param: Or(
        And(param['v']==sym['a'](sym['bot']),param['v']!=sym['witness_value']),
        btw(sym,sym['a'](sym['bot']),param['v'],sym['witness_value'])
    )
    
    bin_counted_v = BinaryFreeRank(counted,v_value)
    rank_agg_v = ParPointwiseFreeRank(bin_counted_v,v_value)

    rank2 = rank_agg_v
    proof2 = LivenessProof(prop2,rank2,rho2,phi2,[psi2])
    print("checking P2") ; proof2.check_proof(ts)

    #P3 : starting in a state where 'bot' holds a unique value eventually only 'bot' will be privileged
    r3 = r1
    p3 = q2
    q3 = lambda sym: And(
        priv(sym,sym['bot']),
        ForAll(X,Implies(X!=sym['bot'],Not(priv(sym,X))))
    )
    prop3 = LivenessProperty(p3,q3,[r3],[{}])

    rho3 = rho1
    phi3 = lambda sym: And(
        rho3(sym),
        Not(q3(sym)),
        #Not(priv(sym,sym['bot'])),
        ForAll([X,Y],Implies(And(sym['leq_node'](X,Y),sym['a'](Y)==sym['a'](sym['bot'])),sym['a'](X)==sym['a'](sym['bot']))),
    )                                                            
    rank3 = rank1 #same rank works, I had variations with more nuanced things but this is best

    proof3 = LivenessProof(prop3,rank3,rho1,phi3,[psi1])
    print("checking P3") ; proof3.check_proof(ts) 
    

    """
    #it is probably possible to combine all properties, but i haven't figured it out yet.
    prop_combined = LivenessProperty(p1,q3,[r1],[{}])
    rank_combined = LexFreeRank([rank2,rank1])
    #main question is what can we say about phi combined?
    phi_combined = lambda sym: And(
        exists_privilege(sym),
        Not(q3(sym)),
        Or(
            And(phi1(sym),Not(q1(sym))),
            And(phi2(sym),q1(sym),Not(q2(sym))),
            And(phi3(sym),q1(sym),q2(sym))
        )
    )
    proof_combined = LivenessProof(prop_combined,rank_combined,rho1,phi_combined,[psi1])
    print("checking lemmaless") ; proof_combined.check_proof(ts) #reduced doesn't go through
    """


    #P4 : starting in a state where only 'bot' is privledged globally there is a unique privilege in the ring.

    stable = lambda sym: Exists(X,And(
        priv(sym,X),
        ForAll(Y,Implies(Y!=X,Not(priv(sym,Y))))
    ))
    #we need to redefine init for this property
    init4 = q3
    ts4 = TS(sorts,axiom,init4,[tr1],constant_sym,relation_sym,function_sym)
    print("checking P4") ; ts4.check_inductiveness(stable) #requires some sort of induction axiom, the one we used before suffices.
    
    #P5 : starting in a stable state any node eventually gets the privilege
    ts5 = TS(sorts,axiom,stable,[tr1],constant_sym,relation_sym,function_sym)
    
    r5 = r1
    p5 = true
    q5 = lambda sym: priv(sym,sym['node_h'])
    prop5 = LivenessProperty(p5,q5,[r5],[{}])

    rho5 = lambda sym: And(stable(sym),exists_privilege(sym))
    phi5 = lambda sym: And(
        rho5(sym),p5(sym),Not(q5(sym))
    )
    psi5 = lambda sym,param: True

    order_h_last = lambda sym,param1,param2: And(
        Or(param2['n']==sym['node_h'],
            And(sym['leq_node'](param1['n'],param2['n']),sym['leq_node'](sym['node_h'],param1['n']),param1['n']!=sym['node_h']),
            And(sym['leq_node'](param1['n'],param2['n']),sym['leq_node'](param2['n'],sym['node_h'])),
            And(sym['leq_node'](sym['node_h'],param1['n']),param1['n']!=sym['node_h'],sym['leq_node'](param2['n'],sym['node_h']))),param1['n']!=param2['n'])
    
    rank5 = ParLexFreeRank(binary_priv_n,n_dict,order_h_last)
    
    proof5 = LivenessProof(prop5,rank5,rho5,phi5,[psi5])
    print("checking P5") ; proof5.check_proof(ts5)


dijsktra()

"""#old version where P0 is another breakdown: 
#P0 : under fair scheduling globally eventually node 'bot' is privileged
r0 = lambda sym,param : param['n'] == sym['skd']
sort_dict = {'n' : Node}
p0 = lambda sym: True
q0 = lambda sym: priv(sym,sym['bot'])
prop0 = ParamLivenessProperty(p0,q0,[r0],[sort_dict])

predicate_priv = lambda sym,n : priv(sym,n)
delta00 = BinaryRankingFunction(predicate_priv)
strict_node_order = lambda sym,n1,n2 : And( sym['leq_node'](n1,n2) , n1!=n2 )
delta01 = OrderLexicographicRank(delta00,Node,strict_node_order)

rho0 = lambda sym: And(
    exists_privilege(sym)
)
phi0 = lambda sym: And(
    rho0(sym),
    Not(q0(sym))
)
psi0 = lambda sym,param: priv(sym,param['n']) #this does not suffice as it is not stable - we need something stronger
psi_minimal0 = lambda sym,param: And(
    psi0(sym,param),
    ForAll(X,Implies(psi0(sym,{'n' : X}),sym['leq_node'](param['n'],X)))
) #this is more subtle: the minimal such node, holds due to induction axiom - in general could be problematic
proof0 = ParamLivenessProof(prop0,delta01,rho0,phi0,[psi_minimal0])
print("checking P0") ; proof0.check_proof(ts) 

    #P1 : starting in a state where 'bot' is privileged and fair sched. eventually node 'bot' is privileged and scheduled

new_init = q0
ts1 = TS(sorts,axiom,new_init,[tr1],constant_sym,relation_sym,function_sym)

r1 = lambda sym,param : param['n'] == sym['skd']
sort_dict = {'n' : Node}
p1 = true
q1 = lambda sym: And(priv(sym,sym['bot']),sym['skd']==sym['bot'])
prop1 = ParamLivenessProperty(p1,q1,[r1],[sort_dict])

rho1 = true 
phi1 = lambda sym: And(rho1(sym),Not(q1(sym)),q0(sym))
psi1 = lambda sym,param: param['n']==sym['bot']
delta1 = BinaryRankingFunction(true) #trivial ranking function - because we just need to see fairness once.

proof1 = ParamLivenessProof(prop1,delta1,rho1,phi1,[psi1])
#print("checking P1") ; proof1.check_proof(ts1)
"""
"""
    #perm rank
    i_dict = {'i':Node}
    j_dict = {'j':Node}
    ij_dict = i_dict | j_dict
    alpha_ij = lambda sym,param: And(
        priv(sym,param['i']),
        sym['leq_node'](param['i'],param['j'])
    )
    bin_ij = BinaryFreeRank(alpha_ij,ij_dict)
    rank_agg_j = ParPointwiseFreeRank(bin_ij,j_dict)

    hints = [{'i':hint_skd}]
    rank_agg_i = ParPermute2FreeRank(rank_agg_j,i_dict,{},hints,hints)
    """
#psi1 = lambda sym,param: If(param['n']==sym['bot'],ForAll(X,Implies(X!=sym['bot'],Not(priv(sym,X)))),priv(sym,param['n']))
#psi_minimal1 = lambda sym,param: And(
#    psi1(sym,param),
#    ForAll(X,Implies(psi1(sym,{'n' : X}),sym['leq_node'](param['n'],X))))
"""counted = lambda sym,value: Or(
    value == sym['a'](sym['bot']),
    ForAll(R,Implies(btw(sym,sym['a'](sym['bot']),R,value),
        Exists(X,sym['a'](X)==R))))
delta_distance_special_new = BinaryRankingFunction(counted)
"""
