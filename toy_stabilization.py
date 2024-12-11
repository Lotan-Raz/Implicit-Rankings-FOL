from z3 import *
from ts import *

def toy_stab():

    #there are multiple tokens in a line, in any move a node that wakes up sends its token to its right neighbor, 
    #except for the top, which vanishes the token (originally i wrote that it moves it to itself, but this is nicer?)

    true = lambda sym: z3.BoolVar(True)

    print("toy stabilization")

    Node = DeclareSort('Node')
    sorts = [Node]
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    
    constant_sym = { 'skd_pre' : Node,
                     #'skd_post' : Node,
                     'top' : Node,
                     }
    relation_sym = {'leq_node' : [Node,Node],
                    'token' : [Node],
    }
    function_sym = {'next' : [Node,Node]}    
    def init(sym):
        return Exists([X,Y],And(X!=Y,sym['token'](X),sym['token'](Y)))
    
    def succ_node(sym,u,v):
        #line_succ
        return Or(
            And(u==sym['top'],v==sym['top']),
            And(u!=v,
            sym['leq_node'](u,v),
            ForAll(W,Or(sym['leq_node'](v,W),sym['leq_node'](W,u))))
        )
    def axiom_leq_node(sym):
        return ForAll([X,Y,Z],And(
        Implies(And(sym['leq_node'](X,Y),sym['leq_node'](Y,Z)),sym['leq_node'](X,Z)),
        Implies(And(sym['leq_node'](X,Y),sym['leq_node'](Y,X)),X==Y),
        Or(sym['leq_node'](X,Y),sym['leq_node'](Y,X)),
        sym['leq_node'](X,sym['top']),
        succ_node(sym,X,sym['next'](X)),
        ))

    def axiom(sym):
        return And(axiom_leq_node(sym))

    def priv(sym,x):
        return sym['token'](x)
    
    def move(sym1,sym2,x):
        return And(
            Not(sym2['token'](x)),
            sym2['token'](sym1['next'](x)),
            ForAll(X,Implies(And(X!=x,X!=sym1['next'](x)),
                             sym2['token'](X)==sym1['token'](X)))
        )
    
    def move_idle(sym1,sym2,x):
        return ForAll(X,sym2['token'](X)==sym1['token'](X))

    param_wakeup = {'n' : Node}
    def tr_wakeup(sym1,sym2,param):
        return And(
        sym1['skd_pre']==param['n'],
        #sym2['skd_post']==param['n'],
        sym2['top']==sym1['top'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        ForAll(X,sym2['next'](X)==sym1['next'](X)),
        Or(
            And(priv(sym1,param['n']),move(sym1,sym2,param['n'])),
            And(Not(priv(sym1,param['n'])),move_idle(sym1,sym2,param['n']))
        )
    )
    
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)
    #ts.bounded_check([true,true])

    def unique_token(sym):
        return ForAll([X,Y],Implies(
            And(priv(sym,X),priv(sym,Y)),
            X==Y),
        )

    #r = lambda sym, param: param['n'] == sym['skd_pre']
    #more proper fairness:
    r = lambda sym,param: priv(sym,sym['skd_pre'])
    #sort_dict = {'n' : Node}
    sort_dict = {}
    p = lambda sym: True
    q = unique_token
    prop = LivenessProperty(p,q,[r],[sort_dict])
    """
    delta_count = CountRank(priv,Node) #only conserved, not reduced, just counting the number of privileges:

    #counting the number of elements (x,y) such that x is privileged and y >=x :
    pred = lambda sym,x,y: And(priv(sym,x),sym['leq_node'](x,y))
    delta_pair_count = SumBinaryPred(pred,Node,Node)
    #delta_pair_count.print_reduced(ts)    

    strict_order = lambda sym,x,y: And(sym['leq_node'](x,y),x!=y)
    free_rank = BinaryRankingFunction(priv)


    delta_lex = OrderLexicographicRank(free_rank,Node,strict_order)

    """
    
    """
    #the more generalized construction, counting the same thing as the pair count.
    param1 = {'x':Node,'y':Node}
    predicate1 = lambda sym,param: And(priv(sym,param['x']),sym['leq_node'](param['x'],param['y']))
    rank1 = BinaryFreeRank(predicate1,param1)


    param2 = {'x':Node}
    param2_quant = {'y' : Node}
    hint2_reduced = lambda sym1,sym2,param1,param2,parame: parame['y']==param1['x'] #hint was not necessary, added to test the hints
    rank2 = ParPointwiseFreeRank(rank1,param2_quant,param2,
                                   #hint2_reduced
                                   )

    #print("nohint");rank2.print_reduced(ts)
    param3 = {}
    hint3_permute = lambda sym1,sym2,param1,param2,paramA,paramB: Or(
        And(sym1['next'](paramA['x'])==paramB['x'],paramA['x']==sym1['skd_pre']),
        And(paramA['x']==paramB['x'],paramA['x']==sym1['skd_pre'])
     )
    #paramA['x'] is where the reduction is, paramA,B['x'] are the permuted
    param3_quant = {'x' : Node}
    rank3 = ParPermute2FreeRank(rank2,param3_quant,param3,
                                  hint3_permute
                                  )

    rank3.print_reduced(ts)
    """
    param1 = {'x':Node,'y':Node}
    predicate1 = lambda sym,param: And(priv(sym,param['x']),sym['leq_node'](param['x'],param['y']))
    rank1 = BinaryFreeRank(predicate1,param1)
    param2 = {'x':Node}
    param2_quant = {'y' : Node}
    param3 = {}
    param3_quant = {'x' : Node}

    #hints by terms:
    hint_y = lambda sym1,sym2,param1,param2: param1['x']
    hint_y2 = lambda sym1,sym2,param1,param2: sym1['top']
    hint1 = {'y' : hint_y}
    hint2 = {'y' : hint_y2}
    rank2_hint = ParPointwiseFreeRank(rank1,param2_quant,
                                            param2,
                                            #[hint1],
                                            )
    #print("empty_hint");rank2_hint.print_reduced(ts); rank2_hint.print_conserved(ts)

    hint_xA = lambda sym1,sym2,param1,param2: sym1['skd_pre']
    hint_xB1 = lambda sym1,sym2,param1,param2: sym1['skd_pre']
    hint_xB2 = lambda sym1,sym2,param1,param2: sym1['next'](sym1['skd_pre'])
    hint_e = lambda sym1,sym2,param1,param2: sym1['skd_pre']
    hints_A  = [{'x':hint_xA}]
    hints_B = [{'x':hint_xB1},{'x':hint_xB2}]
    hints_e = [{'x' : hint_e}]
    rank3_hint = ParPermute2FreeRank(rank2_hint,param3_quant,{},
                                       #[{'x':hint_xA}],[{'x':hint_xA}],[{'x':hint_xB2}]
                                       )# I did simpler hints to make what i want for the paper, but actually with no hints it works better, or you need hints_B
    #rank3_hint.print_conserved(ts)
    #rank3_hint.print_reduced(ts)


    #Few variations on hinting in permutation rankings - not related to the example

    rank_test = ParPermFreeRank(
        BinaryFreeRank(lambda sym,param : sym['token'](param['x']),{'x':Node}),
        {'x':Node},{},2,hints_e,hints_B
        )

    rank_test = ParPermFreeRank_variant(
        BinaryFreeRank(lambda sym,param : sym['token'](param['x']),{'x':Node}),
        {'x':Node},{},2,
        [([{'x':hint_xB1},{'x':hint_xB1}],[{'x':hint_xB2},{'x':hint_xB1}]),([{'x':hint_xB1},{'x':hint_xB1}],[{'x':hint_xB1},{'x':hint_xB1}])],
        [([{'x':hint_xB1},{'x':hint_xB1}],[{'x':hint_xB2},{'x':hint_xB1}],{'x':hint_xB1})],)
    #rank_test.print_conserved(ts)
    rank_test.print_reduced(ts)

    rank_test = ParPermFreeRank_bounded(
        BinaryFreeRank(lambda sym,param : sym['token'](param['x']),{'x':Node}),
        {'x':Node},{},2,[],[{'x':hint_xB1},{'x':hint_xB2}]
        )
    #reduced not ready
    

    rho = lambda sym: And(Exists(X,sym['token'](X)))
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    #psi = lambda sym,param: And(sym['token'](param['n']),param['n']!=sym['top'])
    psi = lambda sym,param: True
    proof = LivenessProof(prop,rank3_hint,rho,phi,[psi])

    import time
    start_time = time.time()
    #proof.check_proof(ts) 
    end_time = time.time()
    runtime = end_time - start_time
    print(runtime)

    """
    ranklin = ParLinFreeRank(BinaryFreeRank(lambda sym,param:True),
                             {'x':Node},
                             lambda sym,param_quant,param_free: priv(sym,param_quant['x']),
                             lambda sym,param1,param2 : And(sym['leq_node'](param2['x'],param1['x']),param1['x']!=param2['x']),
                             {},
                             hints_B)
    ranklin.print_reduced(ts)

    prooflin = LivenessProof(prop,ranklin,rho,phi,[psi])
    #prooflin.check_proof(ts)#doesnt work
    """

    





toy_stab()