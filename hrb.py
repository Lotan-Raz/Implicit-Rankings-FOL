from z3 import *
from ts import *
from timers import *

#HRB from Berkovits

Node = DeclareSort('Node')
QuorumA = DeclareSort('Quorum_A')
QuorumB = DeclareSort('Quorum_B')
sorts = [Node,QuorumA,QuorumB]

constant_sym = {
}
relation_sym = {
    # Immutable relations
    'member_a': [Node, QuorumA],
    'member_b': [Node, QuorumB],
    'member_fa': [Node],
    'member_fc': [Node],
    'member_fs': [Node],
    'member_fi': [Node],
    
    # Mutable relations
    'rcv_init': [Node],
    'accept': [Node],
    'sent_msg': [Node, Node],
    'rcv_msg': [Node, Node],
    'sent_msg_proj': [Node],
}
function_sym = {
}

def axiom(sym):
    B = Const('B', QuorumB)
    A_BP = Const('A_BP', QuorumA)
    B_CF = Const('B_CF', QuorumB)
    A = Const('A', QuorumA)
    N = Const('N', Node)
    
    return And(
        Exists(B, ForAll(N, Implies(sym['member_b'](N, B), 
            And(Not(sym['member_fa'](N)), Not(sym['member_fc'](N)), Not(sym['member_fs'](N)), Not(sym['member_fi'](N)))))),
        ForAll(A_BP, Exists(N, And(sym['member_a'](N, A_BP), Not(sym['member_fa'](N)), Not(sym['member_fs'](N))))),
        ForAll(B_CF, Exists(A, ForAll(N, Implies(sym['member_a'](N, A), 
            And(sym['member_b'](N, B_CF), Not(sym['member_fa'](N)), Not(sym['member_fi'](N))))))),
        ForAll(N, Not(And(sym['member_fc'](N), sym['member_fi'](N)))),
        ForAll(N, Not(And(sym['member_fc'](N), sym['member_fs'](N)))),
        ForAll(N, Not(And(sym['member_fc'](N), sym['member_fa'](N)))),
        ForAll(N, Not(And(sym['member_fi'](N), sym['member_fs'](N)))),
        ForAll(N, Not(And(sym['member_fi'](N), sym['member_fa'](N)))),
        ForAll(N, Not(And(sym['member_fs'](N), sym['member_fa'](N))))
    )

def init(sym):
    X, Y = Consts('X Y', Node)
    return And(
        ForAll(X, Not(sym['accept'](X))),
        ForAll([X, Y], Not(sym['sent_msg'](X, Y))),
        ForAll(X, Not(sym['sent_msg_proj'](X))),
        ForAll([X, Y], Not(sym['rcv_msg'](X, Y))),
    )

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
        ForAll(N, sym2['member_fi'](N) == sym1['member_fi'](N))
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
        ForAll(N1,If(N1==n,
                    sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                    sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
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
                ForAll(N1,If(N1==n,
                            sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                            sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
            ),
            And(
                ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
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
                ForAll(N1,If(N1==n,
                            sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                            sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
                ),
                And(
                ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
                )
            ),
            And(
                ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
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
        Implies(
            sym1['sent_msg_proj'](n),
            Exists(N,sym1['sent_msg'](n,N))
        ), #instrumentation is right
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
        ForAll(N1,If(N1==n,
                    sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                    sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
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
                Implies(
                    sym1['sent_msg_proj'](n),
                    Exists(N,sym1['sent_msg'](n,N))
                ), #instrumentation is right
                ForAll([N1,N2],Implies(sym2['sent_msg'](N1,N2),Or(
                    sym1['sent_msg'](N1,N2),
                    N1==n
                ))),#only messages from n are sent
                ForAll([N1,N2],Implies(sym1['sent_msg'](N1,N2),sym2['sent_msg'](N1,N2))),#messages are not deleted.
                ForAll(N1,If(N1==n,
                            sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                            sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
                ),
                And(
                ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
                )
            ),
            And(
                ForAll([N1, N2], sym2['sent_msg'](N1, N2) == sym1['sent_msg'](N1, N2)),
                ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
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
        ForAll(N1,If(N1==n,
                    sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                    sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
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
        ForAll(N,sym2['sent_msg_proj'](N)==sym1['sent_msg_proj'](N))
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

        Implies(
            sym1['sent_msg_proj'](n),
            Exists(N,sym1['sent_msg'](n,N))
        ), #instrumentation is right
        ForAll([N1,N2],Implies(N1!=n,sym2['sent_msg'](N1,N2)==sym1['sent_msg'](N1,N2))),#arbitrary creation of messages from n
        ForAll([N1,N2],Implies(sym1['sent_msg'](N1,N2),sym2['sent_msg'](N1,N2))),#messages are not deleted.
        ForAll(N1,If(N1==n,
                    sym2['sent_msg_proj'](N1)==Exists(N2,sym2['sent_msg'](N1,N2)),
                    sym2['sent_msg_proj'](N1)==sym1['sent_msg_proj'](N1))),
    )                     
tr8 = ('tr8',param_faulty_send_a,trans_faulty_send_a)

ts = TS(sorts,axiom,init,[tr1,tr2,tr3,tr4,tr5,tr6,tr7,tr8],constant_sym,relation_sym,function_sym)

#bounded model checking
#ts.bounded_check([true,true]) 

#definitions 
def obedient(sym,n):
    return And(Not(sym['member_fs'](n)),Not(sym['member_fa'](n)))

def symmetric(sym,n):
    return And(Not(sym['member_fi'](n)),Not(sym['member_fa'](n)))

def correct(sym,n):
    return And(Not(sym['member_fi'](n)),Not(sym['member_fa'](n)),Not(sym['member_fs'](n)),Not(sym['member_fc'](n)))

def system_invariant(sym):
    N1 = Const('N1', Node)
    N2 = Const('N2', Node)
    M = Const('M', Node)
    N = Const('N',Node)
    A = Const('A', QuorumA)
    B = Const('B', QuorumB)
    return And(
        Implies(
            Exists(N, obedient(sym,N) & sym['accept'](N)),
            Exists(M, obedient(sym,M) & sym['rcv_init'](M))
        ),
        ForAll([N1,N2],Implies(
            sym['sent_msg'](N1,N2),
            sym['sent_msg_proj'](N1)
        )),
        ForAll(N1,Implies(
            sym['sent_msg_proj'](N1),
            Exists(N2,sym['sent_msg'](N1,N2))
        )),
        ForAll([N1,N2],Implies(
            And(symmetric(sym,N1),sym['sent_msg_proj'](N1)),
            sym['sent_msg'](N1,N2)
        )),
        ForAll([N1,N2],Implies(
            And(obedient(sym,N2),sym['rcv_msg'](N1,N2)),
            sym['sent_msg'](N1,N2)
        )),
        ForAll([N1,N2],Implies(
            And(obedient(sym,N1),sym['sent_msg'](N1,N2),Not(sym['rcv_init'](N1))),
            Exists(A,ForAll(M,Implies(sym['member_a'](M,A),sym['sent_msg_proj'](M)))),
        )),
        ForAll(N1,Implies(
            And(obedient(sym,N1),sym['accept'](N1)),
            Exists(B,ForAll(M,Implies(sym['member_b'](M,B),sym['sent_msg_proj'](M))))
        )),
        Implies(
            Exists(A,ForAll(M,Implies(And(sym['member_a'](M,A),obedient(sym,M)),sym['sent_msg_proj'](M)))),
            Exists(N,And(obedient(sym,N),sym['rcv_init'](N)))
        ),     
    )

simplified_formula = foltl_nnf(
        And(
            ForAll(T,G(F(scheduled(T)))),
            F(And(pc2(skolem_thread),G(Not(pc3(skolem_thread)))))
        )
    )


