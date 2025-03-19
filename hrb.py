from z3 import *
from ts import *
from timers import *

#HRB from Berkovits
#currently not encoding the finiteness, and not checking side conditions
#currently commented out sent_msg_proj but maybe we do need it

Node = DeclareSort('Node')
QuorumA = DeclareSort('Quorum_A')
QuorumB = DeclareSort('Quorum_B')
sorts = [Node,QuorumA,QuorumB]

def create_ts():
    constant_sym = {
        # 'witness_exists_correct' : Node, #immutable?
    }
    relation_sym = {
        # Immutable relations
        'member_a': [Node, QuorumA],
        'member_b': [Node, QuorumB],
        'member_fa': [Node],
        'member_fc': [Node],
        'member_fs': [Node],
        'member_fi': [Node],
        'correct': [Node],
        'obedient': [Node],
        'symmetric': [Node],
        
        # Mutable relations
        'rcv_init': [Node],
        'accept': [Node],
        'sent_msg': [Node, Node],
        'rcv_msg': [Node, Node],
        # 'sent_msg_proj': [Node],
    }
    function_sym = {
    }

    def axiom_system(sym):
        B = Const('B', QuorumB)
        A_BP = Const('A_BP', QuorumA)
        B_CF = Const('B_CF', QuorumB)
        A = Const('A', QuorumA)
        N = Const('N', Node)
        
        return And(
            #just to expplain to myself
            #there is a B quorum that has all correct nodes
            #in every A quorum there is a node that is obedient (that is, someone has to check something - i guess then these are large quorums?)
            #every B quorum has an A quroum that has only symmetric nodes from it (why is it important i dont know)
            Exists(B, ForAll(N, Implies(sym['member_b'](N, B), sym['correct'](N)))),
            ForAll(A_BP, Exists(N, And(sym['member_a'](N, A_BP), sym['obedient'](N)))),
            ForAll(B_CF, Exists(A, ForAll(N, Implies(sym['member_a'](N, A), And(sym['member_b'](N, B_CF), sym['symmetric'](N)))))),
            ForAll(N, Not(And(sym['member_fc'](N), sym['member_fi'](N)))),
            ForAll(N, Not(And(sym['member_fc'](N), sym['member_fs'](N)))),
            ForAll(N, Not(And(sym['member_fc'](N), sym['member_fa'](N)))),
            ForAll(N, Not(And(sym['member_fi'](N), sym['member_fs'](N)))),
            ForAll(N, Not(And(sym['member_fi'](N), sym['member_fa'](N)))),
            ForAll(N, Not(And(sym['member_fs'](N), sym['member_fa'](N))))
        )

    def axiom_witness(sym):
        N = Const('N', Node)
        return Implies(
            Exists(N,sym['correct'](N)),
            sym['correct'](sym['witness_exists_correct'])
        )

    def axiom_derived_relations(sym):
        N = Const('N', Node)
        return And(
            ForAll(N,sym['obedient'](N)==And(Not(sym['member_fs'](N)),Not(sym['member_fa'](N)))),
            ForAll(N,sym['symmetric'](N)==And(Not(sym['member_fi'](N)),Not(sym['member_fa'](N)))),
            ForAll(N,sym['correct'](N)==And(Not(sym['member_fi'](N)),Not(sym['member_fa'](N)),Not(sym['member_fs'](N)),Not(sym['member_fc'](N)))),
        )

    def axiom(sym):
        return And(
            axiom_system(sym),
            # axiom_witness(sym),
            axiom_derived_relations(sym)
        )

    def init(sym):
        X, Y = Consts('X Y', Node)
        return And(
            ForAll(X, Not(sym['accept'](X))),
            ForAll([X,Y], Not(sym['sent_msg'](X, Y))),
            # ForAll(X, Not(sym['sent_msg_proj'](X))),
            ForAll([X,Y], Not(sym['rcv_msg'](X, Y))),
        )

    def create_transitions():

        def immutable(sym1, sym2):
            N = Const('N', Node)
            A = Const('A', QuorumA)
            B = Const('B', QuorumB)
            return And(
                ForAll([N, A], sym2['member_a'](N, A) == sym1['member_a'](N, A)),
                ForAll([N, B], sym2['member_b'](N, B) == sym1['member_b'](N, B)),
                ForAll(N, sym2['member_fa'](N) == sym1['member_fa'](N)),
                ForAll(N, sym2['member_fc'](N) == sym1['member_fc'](N)),
                ForAll(N, sym2['member_fs'](N) == sym1['member_fs'](N)),
                ForAll(N, sym2['member_fi'](N) == sym1['member_fi'](N)),
                # sym2['witness_exists_correct'] == sym1['witness_exists_correct'], #NECESSARY?
                ForAll(N, sym2['correct'](N) == sym1['correct'](N)),
                ForAll(N, sym2['obedient'](N) == sym1['obedient'](N)),
                ForAll(N, sym2['symmetric'](N) == sym1['symmetric'](N)),
            )

        param_receive_init = {'n': Node}
        def trans_receive_init(sym1,sym2,param):
            N1 = Const('N1',Node)
            N2 = Const('N2',Node)
            N = Const('N',Node)
            n = param['n']
            return And(
                #guard:
                sym1['rcv_init'](n),

                #immutable says that all immutable symbols do not change
                immutable(sym1,sym2),
                ForAll(N,sym2['rcv_init'](N)==sym1['rcv_init'](N)),
                ForAll(N,sym2['accept'](N)==sym1['accept'](N)),
                ForAll([N,N1],sym2['rcv_msg'](N,N1)==sym1['rcv_msg'](N,N1)),

                #rest of the transition
                #sent_msg(n,N) := true
                ForAll([N1,N2],sym2['sent_msg'](N1,N2)==Or(sym1['sent_msg'](N1,N2),N1==n)),
                #sent_msg_proj(n) := exists N. sent_msg(n,N);
                # ForAll(N1,If(N1==n,
                #             sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                #             sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
            )                     
        tr1 = ('tr1',param_receive_init,trans_receive_init)

        param_receive_msg = {'s': Node, 'n': Node}
        def trans_receive_msg(sym1, sym2, param):
            s = param['s']
            n = param['n']
            N1 = Const('N1', Node)
            N2 = Const('N2', Node)
            A = Const('A', QuorumA)
            B = Const('B', QuorumB)
            N = Const('N', Node)
            return And(
                sym1['sent_msg'](s, n),
                
                immutable(sym1, sym2),
                ForAll(N,sym2['rcv_init'](N)==sym1['rcv_init'](N)),
                ForAll([N1, N2], sym2['rcv_msg'](N1, N2) == Or(sym1['rcv_msg'](N1, N2), And(N1 == s, N2 == n))),
                If(Exists(B,ForAll(N,Implies(sym1['member_b'](N,B),sym2['rcv_msg'](N,n)))),
                    ForAll(N,sym2['accept'](N)==Or(sym1['accept'](N),N==n)),
                    ForAll(N,sym2['accept'](N)==sym1['accept'](N)),
                ),
                If(Exists(A,ForAll(N,Implies(sym1['member_a'](N,A),sym1['rcv_msg'](N,n)))),
                    And(
                        ForAll([N1,N2],sym2['sent_msg'](N1,N2)==Or(sym1['sent_msg'](N1,N2),N1==n)),
                        # ForAll(N1,If(N1==n,
                        #             sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                        #             sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
                    ),
                    And(
                        ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                        # ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
                    )
                )
            )   
        tr2 = ('tr2', param_receive_msg, trans_receive_msg)

        param_receive_msg_c = {'s': Node, 'n': Node}
        def trans_receive_msg_c(sym1, sym2, param):
            s = param['s']
            n = param['n']
            N1 = Const('N1', Node)
            N2 = Const('N2', Node)
            A = Const('A', QuorumA)
            B = Const('B', QuorumB)
            N = Const('N', Node)
            return And(
                sym1['sent_msg'](s, n),
                sym1['member_fc'](n),
                
                immutable(sym1, sym2),
                ForAll(N,sym2['rcv_init'](N)==sym1['rcv_init'](N)),
                ForAll([N1, N2], sym2['rcv_msg'](N1, N2) == Or(sym1['rcv_msg'](N1, N2), And(N1 == s, N2 == n))),
                If(Exists(B,ForAll(N,Implies(sym1['member_b'](N,B),sym2['rcv_msg'](N,n)))),
                    ForAll(N,sym2['accept'](N)==Or(sym1['accept'](N),N==n)),
                    ForAll(N,sym2['accept'](N)==sym1['accept'](N)),
                ),
                If(Exists(A,ForAll(N,Implies(sym1['member_a'](N,A),sym1['rcv_msg'](N,n)))),
                    Or(
                        And(
                        ForAll([N1,N2],sym2['sent_msg'](N1,N2)==Or(sym1['sent_msg'](N1,N2),N1==n)),
                        # ForAll(N1,If(N1==n,
                        #             sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                        #             sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
                        ),
                        And(
                        ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                        # ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
                        )
                    ),
                    And(
                        ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                        # ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
                    )
                )
            )   
        tr3 = ('tr3', param_receive_msg_c, trans_receive_msg_c)

        param_receive_init_i = {'n': Node}
        def trans_receive_init_i(sym1,sym2,param):
            N1 = Const('N1',Node)
            N2 = Const('N2',Node)
            N = Const('N',Node)
            n = param['n']
            return And(
                #guard:
                sym1['member_fi'](n),
                sym1['rcv_init'](n),
                # Implies(
                #     sym1['sent_msg_proj'](n),
                #     Exists(N,sym1['sent_msg'](n,N))
                # ), #instrumentation is right
                immutable(sym1,sym2),
                ForAll(N,sym2['rcv_init'](N)==sym1['rcv_init'](N)),
                ForAll(N,sym2['accept'](N)==sym1['accept'](N)),
                ForAll([N,N1],sym2['rcv_msg'](N,N1)==sym1['rcv_msg'](N,N1)),

                #sent_msg(n,N) := *; assume old sent_msg(n,N) -> sent_msg(n,N);
                ForAll([N1,N2],Implies(sym2['sent_msg'](N1,N2),Or(
                    sym1['sent_msg'](N1,N2),
                    N1==n
                ))),#only messages from n are sent
                ForAll([N1,N2],Implies(sym1['sent_msg'](N1,N2),sym2['sent_msg'](N1,N2))),#messages are not deleted.
                # ForAll(N1,If(N1==n,
                #             sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                #             sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
            )                     
        tr4 = ('tr4',param_receive_init_i,trans_receive_init_i)

        param_receive_msg_i = {'s': Node, 'n': Node}
        def trans_receive_msg_i(sym1, sym2, param):
            s = param['s']
            n = param['n']
            N1 = Const('N1', Node)
            N2 = Const('N2', Node)
            A = Const('A', QuorumA)
            B = Const('B', QuorumB)
            N = Const('N', Node)
            return And(
                sym1['member_fi'](n),
                sym1['sent_msg'](s, n),
                
                immutable(sym1, sym2),
                ForAll(N,sym2['rcv_init'](N)==sym1['rcv_init'](N)),
                ForAll([N1, N2], sym2['rcv_msg'](N1, N2) == Or(sym1['rcv_msg'](N1, N2), And(N1 == s, N2 == n))),
                If(Exists(B,ForAll(N,Implies(sym1['member_b'](N,B),sym2['rcv_msg'](N,n)))),
                    ForAll(N,sym2['accept'](N)==Or(sym1['accept'](N),N==n)),
                    ForAll(N,sym2['accept'](N)==sym1['accept'](N)),
                ),
                If(Exists(A,ForAll(N,Implies(sym1['member_a'](N,A),sym1['rcv_msg'](N,n)))),
                    Or(
                        And(
                        #sent_msg(n,N) := *; assume old sent_msg(n,N) -> sent_msg(n,N);
                        # Implies(
                        #     sym1['sent_msg_proj'](n),
                        #     Exists(N,sym1['sent_msg'](n,N))
                        # ), #instrumentation is right
                        ForAll([N1,N2],Implies(sym2['sent_msg'](N1,N2),Or(
                            sym1['sent_msg'](N1,N2),
                            N1==n
                        ))),#only messages from n are sent
                        ForAll([N1,N2],Implies(sym1['sent_msg'](N1,N2),sym2['sent_msg'](N1,N2))),#messages are not deleted.
                        # ForAll(N1,If(N1==n,
                        #             sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                        #             sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
                        ),
                        And(
                        ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                        # ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
                        )
                    ),
                    And(
                        ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                        # ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
                    )
                )
            )   
        tr5 = ('tr5', param_receive_msg_i, trans_receive_msg_i)

        param_faulty_send_s = {'n': Node}
        def trans_faulty_send_s(sym1,sym2,param):
            N1 = Const('N1',Node)
            N2 = Const('N2',Node)
            N = Const('N',Node)
            n = param['n']
            return And(
                sym1['member_fs'](n),

                immutable(sym1,sym2),
                ForAll(N,sym2['rcv_init'](N)==sym1['rcv_init'](N)),
                ForAll(N,sym2['accept'](N)==sym1['accept'](N)),
                ForAll([N,N1],sym2['rcv_msg'](N,N1)==sym1['rcv_msg'](N,N1)),

                ForAll([N1,N2],sym2['sent_msg'](N1,N2)==Or(sym1['sent_msg'](N1,N2),N1==n)),
                # ForAll(N1,If(N1==n,
                #             sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                #             sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
            )                     
        tr6 = ('tr6',param_faulty_send_s,trans_faulty_send_s)

        param_faulty_state_sa = {'n': Node}
        def trans_faulty_state_sa(sym1,sym2,param):
            N1 = Const('N1',Node)
            N2 = Const('N2',Node)
            N = Const('N',Node)
            n = param['n']
            return And(
                Or(sym1['member_fs'](n),sym1['member_fa'](n)),

                immutable(sym1,sym2),
                ForAll(N,sym2['rcv_init'](N)==sym1['rcv_init'](N)),
                
                ForAll(N,Implies(
                    N!=n,
                    sym2['accept'](N)==sym1['accept'](N)
                )),    
                ForAll([N,N1],Implies(
                    N1!=n,
                    sym2['rcv_msg'](N,N1)==sym1['rcv_msg'](N,N1)),
                ),

                ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                # ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
            )                     
        tr7 = ('tr7',param_faulty_state_sa,trans_faulty_state_sa)

        param_faulty_send_a = {'n': Node}
        def trans_faulty_send_a(sym1,sym2,param):
            N1 = Const('N1',Node)
            N2 = Const('N2',Node)
            N = Const('N',Node)
            n = param['n']
            return And(
                sym1['member_fa'](n),

                immutable(sym1,sym2),
                ForAll(N,sym2['rcv_init'](N)==sym1['rcv_init'](N)),
                ForAll(N,sym2['accept'](N)==sym1['accept'](N)),
                ForAll([N,N1],sym2['rcv_msg'](N,N1)==sym1['rcv_msg'](N,N1)),

                # Implies(
                #     sym1['sent_msg_proj'](n),
                #     Exists(N,sym1['sent_msg'](n,N))
                # ), #instrumentation is right
                ForAll([N1,N2],Implies(N1!=n,sym2['sent_msg'](N1,N2)==sym1['sent_msg'](N1,N2))),#arbitrary creation of messages from n
                ForAll([N1,N2],Implies(sym1['sent_msg'](N1,N2),sym2['sent_msg'](N1,N2))),#messages are not deleted.
                # ForAll(N1,If(N1==n,
                #             sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                #             sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
            )                     
        tr8 = ('tr8',param_faulty_send_a,trans_faulty_send_a)

        transitions = [tr1,tr2,tr3,tr4,tr5,tr6,tr7,tr8]
        only_correct_transitions = [tr1,tr2]
        print('test case - only correct transitions!')
        return only_correct_transitions

    ts = TS(sorts,axiom,init,create_transitions(),constant_sym,relation_sym,function_sym)
    return ts

ts = create_ts()

#bounded model checking
#ts.bounded_check([true,true]) 

def system_invariant(sym):
    N1 = Const('N1', Node)
    N2 = Const('N2', Node)
    M = Const('M', Node)
    N = Const('N',Node)
    A = Const('A', QuorumA)
    B = Const('B', QuorumB)
    return And(
        # System invariants from ivy file - currently not needed
        # Safety Property: if some obedient node accepted then some obedient node initially received the message
        # Implies(
        #     Exists(N, And(sym['obedient'](N),sym['accept'](N))),
        #     Exists(M, And(sym['obedient'](M),sym['rcv_init'](M)))
        # ),
        # ForAll([N1,N2],Implies(
        #     sym['sent_msg'](N1,N2),
        #     sym['sent_msg_proj'](N1)
        # )),
        # ForAll(N1,Implies(
        #     sym['sent_msg_proj'](N1),
        #     Exists(N2,sym['sent_msg'](N1,N2))
        # )),
        # ForAll([N1,N2],Implies(
        #     And(sym['symmetric'](N1),sym['sent_msg_proj'](N1)),
        #     sym['sent_msg'](N1,N2)
        # )),
        # ForAll([N1,N2],Implies(
        #     And(sym['obedient'](N2),sym['rcv_msg'](N1,N2)),
        #     sym['sent_msg'](N1,N2)
        # )),
        # ForAll([N1,N2],Implies(
        #     And(sym['obedient'](N1),sym['sent_msg'](N1,N2),Not(sym['rcv_init'](N1))),
        #     Exists(A,ForAll(M,Implies(sym['member_a'](M,A),sym['sent_msg_proj'](M)))),
        # )),
        # ForAll(N1,Implies(
        #     And(sym['obedient'](N1),sym['accept'](N1)),
        #     Exists(B,ForAll(M,Implies(sym['member_b'](M,B),sym['sent_msg_proj'](M))))
        # )),
        # Implies(
        #     Exists(A,ForAll(M,Implies(And(sym['member_a'](M,A),sym['obedient'](M)),sym['sent_msg_proj'](M)))),
        #     Exists(N,And(sym['obedient'](N),sym['rcv_init'](N)))
        # ),     
        


        #not from original ivy file
        Implies(
            ForAll([N,M],Implies(
                And(sym['correct'](N),sym['correct'](M)),
                sym['rcv_msg'](N,M)
            )),
            Exists(N,And(sym['correct'](N),sym['accept'](N)))
        ),
        #only for the relay property - they instantiate this invariant only for specific witness nodes because its not EPR

        #invariant forall N,B. correct(N) & ~accept(N) -> exists M. member_b(M,B) & ~rcv_msg(M,N)
        ForAll([N,B],Implies(
            And(sym['correct'](N),Not(sym['accept'](N))),
            Exists(M,And(sym['member_b'](M,B),Not(sym['rcv_msg'](M,N))))
        )),
        # invariant forall N,A. correct(N) & ~sent_msg_proj(N) -> exists M. member_a(M,A) & ~rcv_msg(M,N)
        ForAll([N,A],Implies(
            And(sym['correct'](N),Not(Exists(M,sym['sent_msg'](N,M)))),
            Exists(M,And(sym['member_a'](M,A),Not(sym['rcv_msg'](M,N))))
        )),
    )

correct = Function('correct', Node, BoolSort())
rcv_init = Function('rcv_init', Node, BoolSort())
sent_msg = Function('sent_msg', Node, Node, BoolSort())
rcv_msg = Function('rcv_msg', Node, Node, BoolSort())
obedient = Function('obedient', Node, BoolSort())
accept = Function('accept', Node, BoolSort())
N = Const('N', Node)
M = Const('M', Node)

"""
First Property - Correctness
In words: 
if all obedient nodes initially hold the message and 
all correct nodes eventually send and receive 
then eventually some node accepts
"""

correctness = foltl_nnf(
        And(
            ForAll([N,M],Implies(And(correct(N),rcv_init(N)),F(sent_msg(N,M)))),
            ForAll([N,M],G(Implies(And(sent_msg(N,M),correct(M)),F(rcv_msg(N,M))))),
            ForAll(N,Implies(obedient(N),rcv_init(N))),
            G(ForAll(N,Not(And(correct(N),accept(N)))))
        )
    )

#intuition:
# all correct nodes are obedient so they receive init
# we wait for some correct node to send to all nodes
# we then wait for the message to be received by all nodes in a B quorum that has all the correct nodes
# then any correct node will accept
# giving contradiction to the negated property

timer_system = timer_transition_system(correctness,{})

#print(timer_system.constant_sym)
#print(timer_system.function_sym)
intersection = IntersectionTS(ts, timer_system)
# state_pre = intersection.create_state("_pre")
# state_post = intersection.create_state("_post")
# print(intersection.tr(state_pre.get_dict(),state_post.get_dict()))

def timer_invariant_correctness(sym):
    return And(
        sym['t_<G(ForAll(N, Or(Not(correct(N)), Not(accept(N)))))>']==0,
        ForAll(N,Implies(sym['obedient'](N),sym['rcv_init'](N))),
        ForAll([N,M],Implies(
            And(sym['correct'](N),Not(sym['sent_msg'](N,M))),
            sym['t_<sent_msg(N, M)>'](N,M)>0,
        )),
        ForAll([N,M],sym['t_<G(Or(Or(Not(sent_msg(N, M)), Not(correct(M))), F(rcv_msg(N, M))))>'](N,M)==0),
        ForAll([N,M],Implies(
            And(sym['correct'](M),sym['sent_msg'](N,M),Not(sym['rcv_msg'](N,M))),
            sym['t_<rcv_msg(N, M)>'](N,M)>0,  
        ))
    )

def invariant_correctness(sym):
    return And(
        system_invariant(sym),
        timer_invariant_correctness(sym)
    )

#system ranks
param_NM = {'N':Node,'M':Node}

not_sent_predicate = lambda sym,param: Not(sym['sent_msg'](param['N'],param['M']))
bin_not_sent = BinaryFreeRank(not_sent_predicate,{'N':Node,'M':Node})
pw_not_sent = ParPointwiseFreeRank(bin_not_sent,param_NM)

not_recv_predicate_both_correct = lambda sym,param: And(
    sym['correct'](param['N']),
    sym['correct'](param['M']),
    Not(sym['rcv_msg'](param['N'],param['M']))
)
bin_not_recv = BinaryFreeRank(not_recv_predicate_both_correct,{'N':Node,'M':Node})
pw_not_recv = ParPointwiseFreeRank(bin_not_recv,param_NM)



# param_N = {'N':Node}
# correct_not_accepted = lambda sym,param: And(sym['correct'](param['N']),Not(sym['accept'](param['N'])))
# bin_pw_correct_not_accepted = BinaryFreeRank(correct_not_accepted,param_N)
# pw_correct_not_accepted = ParPointwiseFreeRank(bin_pw_correct_not_accepted,param_N)

#timer ranks
#this should be packaged
param_int = {'x':IntSort()}	
sent_timer = PositionInOrderFreeRank(
    lambda sym,param1,param2 : param1['x']<param2['x'],
    param_int,
    {'x':lambda sym,param:sym['t_<sent_msg(N, M)>'](param['N'],param['M'])},
    param_NM	
)
trivial_rank = BinaryFreeRank(lambda *args:True,param_NM)

correct_and_unsent = lambda sym,param: And(sym['correct'](param['N']),Not(sym['sent_msg'](param['N'],param['M'])))
ow1 = lambda sym,param: Not(correct_and_unsent(sym,param))
sent_timer_for_good = LinFreeRank(
    [sent_timer,trivial_rank],
    [correct_and_unsent,ow1]
)
all_sent_timers = ParPointwiseFreeRank(sent_timer_for_good,param_NM)

#can this be packaged?
rcv_timer = PositionInOrderFreeRank(
    lambda sym,param1,param2 : param1['x']<param2['x'],
    param_int,
    {'x':lambda sym,param:sym['t_<rcv_msg(N, M)>'](param['N'],param['M'])},
    param_NM	
)
trivial_rank = BinaryFreeRank(lambda *args:True,param_NM)

#kind of complicated: before messages are sent trivial rank, after the message is sent and not yet 
#recieved we wait for it to be received and after it is received trivial rank
#perhaps could be simplified
not_sent = lambda sym,param: Not(sym['sent_msg'](param['N'],param['M']))
correct_sent_not_recv = lambda sym,param: And(sym['correct'](param['M']),
                                              sym['correct'](param['N']),
                                              sym['sent_msg'](param['N'],param['M']),
                                              Not(sym['rcv_msg'](param['N'],param['M'])))
ow2 = lambda sym,param: And(Not(correct_sent_not_recv(sym,param)),Not(not_sent(sym,param)))
sent_timer_for_good = LinFreeRank(
    #unintuitive, but the left rank is the "larger" one
    [trivial_rank,rcv_timer,trivial_rank],
    [not_sent,correct_sent_not_recv,ow2]
)
all_rcv_timers = ParPointwiseFreeRank(sent_timer_for_good,param_NM)

rank_correctness = PointwiseFreeRank([
    pw_not_recv,
    pw_not_sent,
    all_sent_timers,
    all_rcv_timers
])  

# proof_correctness = TerminationProof(rank_correctness,invariant_correctness)
# proof_correctness.check_proof(intersection)

"""
Second Property - Relay
In words: 
under the same assumptions
if some correct node accepts
then eventually all correct nodes accept
"""

relay = foltl_nnf(
        And(
            ForAll([N,M],Implies(And(correct(N),rcv_init(N)),F(sent_msg(N,M)))),
            ForAll([N,M],G(Implies(And(sent_msg(N,M),correct(M)),F(rcv_msg(N,M))))),
            F(Exists(N,And(obedient(N),accept(N)))),
            G(Exists(N,And(correct(N),Not(accept(N)))))
        )
    )

#intuition:
# first we wait for some obedient node n0 to accept
# let B0 be the quorum that has all the correct nodes
# and let A0 be the quorum that has only symmetric nodes from B0
# we want to show that eventually all correct nodes accept through B0 
# didn't compeletely get this but this is related to the non-EPR invariants above.

timer_system = timer_transition_system(relay,{})
intersection = IntersectionTS(ts, timer_system)
# print(intersection.constant_sym)

def timer_invariant_relay(sym):
    return And(
        sym['t_<G(Exists(N, And(correct(N), Not(accept(N)))))>']==0,
        ForAll([N,M],Implies(
            And(sym['correct'](N),sym['rcv_init'](N),Not(sym['sent_msg'](N,M))),
            sym['t_<sent_msg(N, M)>'](N,M)>0,
        )),
        ForAll([N,M],sym['t_<G(Or(Or(Not(sent_msg(N, M)), Not(correct(M))), F(rcv_msg(N, M))))>'](N,M)==0),
        ForAll([N,M],Implies(
            And(sym['correct'](M),sym['sent_msg'](N,M),Not(sym['rcv_msg'](N,M))),
            sym['t_<rcv_msg(N, M)>'](N,M)>0,  
        )),
        Or(
            Exists(N,And(sym['obedient'](N),sym['accept'](N))),
            sym['t_<Exists(N, And(obedient(N), accept(N)))>']>0
        )
    )

def invariant_relay(sym):
    return And(
        system_invariant(sym),
        timer_invariant_relay(sym)
    )

#more ranks

not_accept_correct = lambda sym,param: And(sym['correct'](param['N']),Not(sym['accept'](param['N'])))
bin_not_accept = BinaryFreeRank(not_accept_correct,{'N':Node})
pw_not_accept = ParPointwiseFreeRank(bin_not_accept,{'N':Node})

#should be packaged somehow
timer_exists_accept = PositionInOrderFreeRank(
    lambda sym,param1,param2 : param1['x']<param2['x'],
    param_int,
    {'x':lambda sym,param:sym['t_<Exists(N, And(obedient(N), accept(N)))>']},
    {}
)
exists_accept = lambda sym,param: Exists(N, And(sym['obedient'](N), sym['accept'](N)))
not_exists_accept = lambda sym,param: Not(exists_accept(sym,param))
timer_exists_accept_lin = LinFreeRank(
    [timer_exists_accept,trivial_rank],
    [not_exists_accept,exists_accept]
)


#not necessarily important or needed at all
correct_rcv_init_and_unsent = lambda sym,param: And(
    sym['correct'](param['N']),
    sym['rcv_init'](param['N']),
    Not(sym['sent_msg'](param['N'],param['M'])
))
ow3 = lambda sym,param: Not(correct_rcv_init_and_unsent(sym,param))
sent_timer_for_good = LinFreeRank(
    [sent_timer,trivial_rank],
    [correct_rcv_init_and_unsent,ow3]
)
all_sent_timers_refined = ParPointwiseFreeRank(sent_timer_for_good,param_NM)

not_sent = lambda sym,param: Not(sym['sent_msg'](param['N'],param['M']))
correct_sent_not_recv_accept = lambda sym,param: And(sym['correct'](param['M']),
                                              sym['correct'](param['N']),
                                              sym['sent_msg'](param['N'],param['M']),
                                              Not(sym['rcv_msg'](param['N'],param['M'])),
                                              Not(sym['accept'](param['M'])))
ow4 = lambda sym,param: And(Not(correct_sent_not_recv_accept(sym,param)),Not(not_sent(sym,param)))
sent_timer_for_good = LinFreeRank(
    [trivial_rank,rcv_timer,trivial_rank],
    [not_sent,correct_sent_not_recv_accept,ow4]
)
all_rcv_timers_refined = ParPointwiseFreeRank(sent_timer_for_good,param_NM)

#the rank below might be good enough but there is either a problem with the timer ranks or the invariant is not good enough.

rank_relay = PointwiseFreeRank([
    pw_not_sent,
    pw_not_recv,
    pw_not_accept,
    timer_exists_accept_lin,
    all_rcv_timers_refined,
    all_sent_timers_refined
])

proof_relay = TerminationProof(rank_relay,invariant_relay)
proof_relay.check_proof(intersection)
