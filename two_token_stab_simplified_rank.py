from z3 import *
from ts import *
import time

def two_tokens_stabilization():

    # two types of tokens: token_R, token_L
    # when a node wakes up: if it holds token_R it gives it to its right neighbor, 
    # if it holds token_L, it gives it to its left neighbor, if it holds both it goes by token_R, and token_L is lost.
    # bottom and top are special: bottom can only hold token_L, and when it does it gives its right neighbor token_R
    # top can only hold token_R, and when it does it gives its left neighbor token_L
    # this imitates Dijkstra's second protocol

    true = lambda sym: z3.BoolVal(True) 

    print("two_token_stabilization")

    Node = DeclareSort('Node')
    TokenType,(left,right) = EnumSort('TokenType',('L','R'))
    sorts = [Node]
    X = Const('X',Node)
    Y = Const('Y',Node)
    Z = Const('Z',Node)
    W = Const('W',Node)
    T = Const('T',TokenType)

    constant_sym = { 'skd' : Node,
                     'next_skd' : Node,
                     'prev_skd' : Node, #this is the trick we use to optimize the solver
                     'top' : Node,
                     'bot' : Node
                     }
    relation_sym = {'leq_node' : [Node,Node],
                    'token' : [Node,TokenType],
    }
    function_sym = {}

    def init(sym):
        return And(
            Exists(X,Or(sym['token'](X,left),sym['token'](X,right))),
            Not(sym['token'](sym['bot'],right)),
            Not(sym['token'](sym['top'],left)),
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
        succ_node(sym,sym['prev_skd'],sym['skd']),
        succ_node(sym,sym['skd'],sym['next_skd']),
        ))
    
    def small(sym):
        return Exists([X,Y,Z],ForAll(W,Or(X==W,Y==W,Z==W)))

    def axiom(sym):
        return And(axiom_leq_node(sym),#small(sym)
                  )

    def priv_R_normal(sym,x):
        return And(sym['token'](x,right), x != sym['top'], x != sym['bot'])

    def priv_L_normal(sym,x):
        return And(sym['token'](x,left),Not(sym['token'](x,right)),x != sym['top'], x != sym['bot'])

    def priv_R_top(sym,x):
        return And(sym['token'](x,right), x == sym['top'])
    
    def priv_L_bot(sym,x):
        return And(sym['token'](x,left), x == sym['bot'])
                   
    def priv(sym,x):
        return Or(sym['token'](x,left),sym['token'](x,right)) #Exists(T,sym['token'](x,T))
                

    def move_L(sym1,sym2):
        skd = sym1['skd']
        prev_skd = sym1['prev_skd']
        return And(
            ForAll(X,sym2['token'](X,left)==Or(
                And(sym1['token'](X,left),X!=skd),X==prev_skd)),
            ForAll(X,sym2['token'](X,right)==And(sym1['token'](X,right),X!=skd))
            ) #this is also the move top does when it holds token_R
    
    def move_R(sym1,sym2):
        skd = sym1['skd']
        next_skd = sym1['next_skd']
        return And(
            ForAll(X,sym2['token'](X,right)==Or(
                And(sym1['token'](X,right),X!=skd),X==next_skd)),
            ForAll(X,sym2['token'](X,left)==And(sym1['token'](X,left),X!=skd))
            ) #this is also the move bottom does when it holds token_L

    def move_idle(sym1,sym2):
        return And(
            ForAll(X,sym2['token'](X,left)==sym1['token'](X,left)),
            ForAll(X,sym2['token'](X,right)==sym1['token'](X,right)),
            )

    param_wakeup = {}
    def tr_wakeup(sym1,sym2,param):
        skd = sym1['skd']
        return And(
        sym2['top']==sym1['top'],
        sym2['bot']==sym1['bot'],
        ForAll([X,Y],sym2['leq_node'](X,Y)==sym1['leq_node'](X,Y)),
        Or(
            And(priv_R_normal(sym1,skd),move_R(sym1,sym2)),
            And(priv_L_normal(sym1,skd),move_L(sym1,sym2)),
            And(priv_R_top(sym1,skd),move_L(sym1,sym2)),
            And(priv_L_bot(sym1,skd),move_R(sym1,sym2)),
            And(Not(priv(sym1,skd)),move_idle(sym1,sym2))
            )
        )
    
    tr1 = ('wakeup',param_wakeup,tr_wakeup)
    ts = TS(sorts,axiom,init,[tr1],constant_sym,relation_sym,function_sym)

    def unique_token(sym):
        return And(
            ForAll([X,Y],Implies(And(priv(sym,X),priv(sym,Y)),X==Y)), #unique privileged node
            ForAll(X,Not(And(sym['token'](X,right),sym['token'](X,left)))) #unique privilege
            )
    def inv(sym):
        return And(
            Not(sym['token'](sym['bot'],right)),
            Not(sym['token'](sym['top'],left)),
            #Liveness
            Exists(X,priv(sym,X)) #not actually required: just justifies the fairness ass.
            )   
    
    #ts.bounded_check([lambda sym: priv(sym,sym['top']),
    #                  lambda sym: Not(Or(priv(sym,sym['top']),priv(sym,sym['bot']))),
    #                  lambda sym: priv(sym,sym['bot'])])   
    #this succeeds
    
    #ts.bounded_check([lambda sym: And(
    #    sym['skd_pre']!=sym['bot'],
    #    sym['skd_pre']!=sym['top'],
    #    sym['token'](sym['skd_pre'],right),
    #    Not(sym['token'](sym['skd_pre'],left)),
    #    Not(sym['token'](sym['top'],right))
    #                                ), true])
    #this succeeds
    
    #main property we want to prove, and start of proof
    r = lambda sym,param: Implies(Exists(X,priv(sym,X)),priv(sym,sym['skd']))
    p = true
    q = unique_token
    prop = LivenessProperty(p,q,[r],[{}])
    rho = inv
    phi = lambda sym: And(rho(sym),Not(q(sym)))
    psi = lambda sym,param: z3.BoolVal(True)

    #P = N_(x,t) token(x,t)
    param_xt = {'x':Node,'t':TokenType}
    pred_token_xt = lambda sym,param: sym['token'](param['x'],param['t'])
    binary_token_xt = BinaryFreeRank(pred_token_xt,param_xt)

    #hints
    skd_term = lambda sym1,sym2,param1,param2: sym1['skd']
    x_to_skd = {'x':skd_term}
    next_skd_term = lambda sym1,*args : sym1['next_skd']
    prev_skd_term = lambda sym1,*args : sym1['prev_skd']
    x_to_next = {'x':next_skd_term}
    x_to_prev = {'x':prev_skd_term}
    t_to_left = {'t':lambda *args: left}
    t_to_right = {'t':lambda *args: right}
    hints_A = [x_to_skd | t_to_left, x_to_skd | t_to_right]
    hints_B = [x_to_skd | t_to_left, x_to_skd | t_to_right,
                x_to_next | t_to_left, x_to_next | t_to_right,
                x_to_prev | t_to_left, x_to_prev | t_to_right,]

    num_tokens = ParPermute2FreeRank(binary_token_xt,param_xt,{},
                                     hints_A,hints_A,hints_B
                                     )

    ### ranking: (P,D) where P = N_(x,t) token(x,t) (showed left to be conserved)
    ### D = sum_(x,t) V(x,t) where V(x,t) is 0 if x doesn't hold token t, and if it does it gives a bound on the number
    ### of steps x may take until crashing into another privilege.

    param_xti = {'x':Node,'t':TokenType,'i':Node}
    param_i = {'i':Node}

    # specifically, to count V(x,t), we divide into two parts:
    # moves to the right and moves to the left
    # for example, if a node x has a right token:
    # if there is a node z>=x with a left token to its right, V(x,R) = z-x (R) 
    # if there is no such node but node z!=x has R then V(x,R) = n-1-z (L) +   n-1-x (R)
    # if there is no such node, but a node z<x with L: V(x,R) = n-1-x (R) +  n-1 (L)  +   z (R)
    # if node x has a left token:
    # if there is a node z<=x with a right token to its right, V(x,L) = x-z (L)
    # if there is no such node but node z!=x has R then V(x,L) = x (L)  +   z (R)
    # if there is no such node, but a node z>x with R: V(x,L) = x (L) +  n-1 (R) +  n-1-z (L)
    
    ###Trying a simplification:
    counts_for_right_move = lambda sym,param: And(
        pred_token_xt(sym,param),
        Or(
            And(
                #z-x / n-1-x 
                param['t']==right,
                sym['leq_node'](param['x'],param['i']),
                ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y),sym['leq_node'](Y,param['i']),param['i']!=Y),
                                Not(sym['token'](Y,left)))), 
            ),
            And(
                #z / n-1
                param['t']==left,
                ForAll(Y,Implies(And(sym['leq_node'](Y,param['x'])),
                                Not(sym['token'](Y,right)))),
                ForAll(Y,Implies(And(sym['leq_node'](Y,param['i']),param['i']!=Y),
                                Implies(sym['token'](Y,left),Y==param['x'])))
            ),
            And(
                #z
                param['t']==right,
                sym['leq_node'](param['i'],param['x']),
                param['i']!=param['x'],
                ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y)),
                        Not(sym['token'](Y,left)))),
                ForAll(Y,Implies(sym['token'](Y,right),Y==param['x'])),
                ForAll(Y,Implies(And(sym['leq_node'](Y,param['i']),param['i']!=Y),
                                Not(sym['token'](Y,left)))), 
            ),
        )
    )
    counts_for_left_move = lambda sym,param: And(
        pred_token_xt(sym,param),
        Or(
            And(
                #x-z / x  
                param['t']==left,
                sym['leq_node'](param['i'],param['x']),
                ForAll(Y,Implies(And(sym['leq_node'](Y,param['x']),sym['leq_node'](param['i'],Y),param['i']!=Y),
                                Not(sym['token'](Y,right)))),
            ),
            And(
                #n-1-z / n-1
                param['t']==right,
                ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y)),
                                Not(sym['token'](Y,left)))),
                ForAll(Y,Implies(And(sym['leq_node'](param['i'],Y),param['i']!=Y),
                                Implies(sym['token'](Y,right),Y==param['x'])))
            ),
            And(
                #n-1-z
                param['t']==left,
                sym['leq_node'](param['x'],param['i']),
                param['i']!=param['x'],
                ForAll(Y,Implies(And(sym['leq_node'](Y,param['x'])),
                        Not(sym['token'](Y,right)))),
                ForAll(Y,Implies(sym['token'](Y,left),Y==param['x'])),
                ForAll(Y,Implies(And(sym['leq_node'](param['i'],Y),param['i']!=Y),
                                Not(sym['token'](Y,right)))), 
            ),
        )    
    )
    
    binary_counts_for_right = BinaryFreeRank(counts_for_right_move,param_xti)
    binary_counts_for_left = BinaryFreeRank(counts_for_left_move,param_xti)

    x_term = lambda sym1,sym2,param1,param2: param1['x']
    i_to_x = {'i':x_term}
    i_to_skd = {'i':skd_term}
    hints_for_dist = [i_to_x,i_to_skd]

    dist_right = ParPointwiseFreeRank(binary_counts_for_right,param_i,param_xt,
                                      hints_for_dist
                                      )
    dist_left = ParPointwiseFreeRank(binary_counts_for_left,param_i,param_xt,
                                     hints_for_dist
                                     )
    distance_xt = PointwiseFreeRank([dist_left,dist_right],param_xt)

    sum_distances = ParPermute2FreeRank(distance_xt,param_xt,{},
                                          hints_A,hints_A,hints_B ###Here if you remove the hints it times out (you can comment out the line)
                                          )
    rank = LexFreeRank([num_tokens,sum_distances])

    proof = LivenessProof(prop,rank,rho,phi,[psi])
    
    start_time = time.time()
    #proof.check_proof(ts) 
    end_time = time.time()
    runtime = end_time - start_time
    print(f"Runtime: {runtime} seconds")




    
    #Further simplification?
    ty_to_left = {'move':lambda *args: left}
    ty_to_right = {'move':lambda *args: right}

    param_xtyi = {'x':Node,'move':TokenType,'i':Node}

    def predicate_xtyi(sym,param):
        #x is free
        #i is the node index
        #move is the type of move 
        x = param['x']
        return Or(
            And(sym['token'](x,right),
                Or(
                    And(
                        #z-x / n-1-x 
                        param['move']==right, #this now says that this counts for right moves, not right token
                        sym['leq_node'](param['x'],param['i']),
                        ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y),sym['leq_node'](Y,param['i']),param['i']!=Y),
                                        Not(sym['token'](Y,left)))), 
                    ),
                    And(
                        #n-1-z / n-1
                        param['move']==left,
                        ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y)),
                                            Not(sym['token'](Y,left)))),
                        ForAll(Y,Implies(And(sym['leq_node'](param['i'],Y),param['i']!=Y),
                                            Implies(sym['token'](Y,right),Y==param['x'])))
                    ),
                    And(
                        #z
                        param['move']==right,
                        sym['leq_node'](param['i'],param['x']),
                        param['i']!=param['x'],
                        ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y)),
                                Not(sym['token'](Y,left)))),
                        ForAll(Y,Implies(sym['token'](Y,right),Y==param['x'])),
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['i']),param['i']!=Y),
                                        Not(sym['token'](Y,left)))), 
                    )
                )
            ),
            And(sym['token'](x,left),
                Or(
                    And(
                        #x-z / x  
                        param['move']==left,
                        sym['leq_node'](param['i'],param['x']),
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['x']),sym['leq_node'](param['i'],Y),param['i']!=Y),
                                        Not(sym['token'](Y,right)))),
                    ),
                    And(
                        #z / n-1
                        param['move']==right,
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['x'])),
                                        Not(sym['token'](Y,right)))),
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['i']),param['i']!=Y),
                                        Implies(sym['token'](Y,left),Y==param['x'])))
                    ),
                    And(
                        #n-1-z
                        param['move']==left,
                        sym['leq_node'](param['x'],param['i']),
                        param['i']!=param['x'],
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['x'])),
                                Not(sym['token'](Y,right)))),
                        ForAll(Y,Implies(sym['token'](Y,left),Y==param['x'])),
                        ForAll(Y,Implies(And(sym['leq_node'](param['i'],Y),param['i']!=Y),
                                        Not(sym['token'](Y,right)))), 
                    )
                )
            )
        )

    hints_ity = [i_to_x | ty_to_left, i_to_skd | ty_to_left,
                i_to_x | ty_to_right, i_to_skd | ty_to_right]
    binary_xtyi = BinaryFreeRank(predicate_xtyi,param_xtyi)
    sum_ity = ParPointwiseFreeRank(binary_xtyi,{'i':Node,'move':TokenType},{'x':Node},hints_ity)
    sum_x = ParPermFreeRank(sum_ity,{'x':Node},{},1,[x_to_skd],[x_to_skd,x_to_prev,x_to_next])

    rank_variant = LexFreeRank([num_tokens,sum_x])

    proof_variant = LivenessProof(prop,rank_variant,rho,phi,[psi])    


    ##Doesnt work - you cant not have t
    start_time = time.time()
    #proof_variant.check_proof(ts) 
    end_time = time.time()
    runtime = end_time - start_time
    print(f"Runtime: {runtime} seconds")



    #Different simplification? but less elegant than the first one
    def mixed_predicate(sym,param):
        x = param['x']
        t = param['t']
        move = param['move']
        i = param['i']
        return Or(
            And(
                move == right,
                pred_token_xt(sym,param),
                Or(
                    And(
                        #z-x / n-1-x 
                        param['t']==right,
                        sym['leq_node'](param['x'],param['i']),
                        ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y),sym['leq_node'](Y,param['i']),param['i']!=Y),
                                        Not(sym['token'](Y,left)))), 
                    ),
                    And(
                        #z / n-1
                        param['t']==left,
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['x'])),
                                        Not(sym['token'](Y,right)))),
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['i']),param['i']!=Y),
                                        Implies(sym['token'](Y,left),Y==param['x'])))
                    ),
                    And(
                        #z
                        param['t']==right,
                        sym['leq_node'](param['i'],param['x']),
                        param['i']!=param['x'],
                        ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y)),
                                Not(sym['token'](Y,left)))),
                        ForAll(Y,Implies(sym['token'](Y,right),Y==param['x'])),
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['i']),param['i']!=Y),
                                        Not(sym['token'](Y,left)))), 
                    ),
                )
            ),
            And(
                move == left,
                pred_token_xt(sym,param),
                Or(
                    And(
                        #x-z / x  
                        param['t']==left,
                        sym['leq_node'](param['i'],param['x']),
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['x']),sym['leq_node'](param['i'],Y),param['i']!=Y),
                                        Not(sym['token'](Y,right)))),
                    ),
                    And(
                        #n-1-z / n-1
                        param['t']==right,
                        ForAll(Y,Implies(And(sym['leq_node'](param['x'],Y)),
                                        Not(sym['token'](Y,left)))),
                        ForAll(Y,Implies(And(sym['leq_node'](param['i'],Y),param['i']!=Y),
                                        Implies(sym['token'](Y,right),Y==param['x'])))
                    ),
                    And(
                        #n-1-z
                        param['t']==left,
                        sym['leq_node'](param['x'],param['i']),
                        param['i']!=param['x'],
                        ForAll(Y,Implies(And(sym['leq_node'](Y,param['x'])),
                                Not(sym['token'](Y,right)))),
                        ForAll(Y,Implies(sym['token'](Y,left),Y==param['x'])),
                        ForAll(Y,Implies(And(sym['leq_node'](param['i'],Y),param['i']!=Y),
                                        Not(sym['token'](Y,right)))), 
                    ),
                )    
            )
        )
    
    binary_mixed = BinaryFreeRank(mixed_predicate,{'x':Node,'t':TokenType,'move':TokenType,'i':Node})
    sum_move_i = ParPointwiseFreeRank(binary_mixed,
                                      {'i':Node,'move':TokenType},
                                      {'x':Node,'t':TokenType},
                                      hints_ity)
    sum_xt = ParPermute2FreeRank(sum_move_i,{'x':Node,'t':TokenType},{},
                             hints_A,hints_A,hints_B)
    
    rank = LexFreeRank([num_tokens,sum_xt])

    proof = LivenessProof(prop,rank,rho,phi,[psi])
    
    start_time = time.time()
    proof.check_proof(ts) 
    end_time = time.time()
    runtime = end_time - start_time
    print(f"Runtime: {runtime} seconds")




two_tokens_stabilization()