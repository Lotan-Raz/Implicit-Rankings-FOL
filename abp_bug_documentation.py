from z3 import *
from ts import *
from timers import *

#ABP from ivy
#didnt finish writing the transitions

Index = DeclareSort('Index')
Value = DeclareSort('Value')
Data_msg = DeclareSort('Data_msg')
Ack_msg = DeclareSort('Ack_msg')

def create_ts():
    sorts = [Index,Value,Data_msg,Ack_msg]

    constant_sym = {
        'zero_index': Index, #immut
        'bot': Value, #immut 
        'sender_i': Index,
        'sender_gen_i': Index,
        'receiver_i': Index,
        'sk_index' : Index,
    }
    relation_sym = {
        'le_index': [Index, Index], #immut
        'le_data_msg': [Data_msg, Data_msg],
        'le_ack_msg': [Ack_msg, Ack_msg],
        'dbit': [Data_msg], #immut
        'abit': [Ack_msg], #immut
        'sender_bit': [],
        'receiver_bit': [],
        #fairness
        'sender_scheduled': [],
        'receiver_scheduled': [],
        'data_sent': [],
        'data_received': [],
        'ack_sent': [],
        'ack_received': []
    }
    function_sym = {
        'd': [Data_msg, Value], #immut
        'sender_array': [Index, Value],
        'receiver_array': [Index, Value]
    }

    def succ_index(sym,i,j):
        Z = Const('Z', Index)
        return And(
            sym['le_index'](i,j), i!=j,
            ForAll(Z,Implies(And(sym['le_index'](i,Z),i!=Z),sym['le_index'](j,Z)))
        )    

    def index_order_axioms(sym):
        i = Const('i', Index)
        j = Const('j', Index)
        k = Const('k', Index)
        return And(
            ForAll([i, j, k], Implies(And(sym['le_index'](i, j), sym['le_index'](j, k)), sym['le_index'](i, k))),  # Transitivity
            ForAll([i, j], Implies(And(sym['le_index'](i, j), sym['le_index'](j, i)), i == j)),  # Antisymmetry
            ForAll([i, j], Or(sym['le_index'](i, j), sym['le_index'](j, i))),  # Totality
            ForAll(i, sym['le_index'](sym['zero_index'], i))  # zero_index as minimal
        )

    def axiom(sym):
        return And(
            index_order_axioms(sym)
        )

    def init(sym):
        I = Const('I', Index)
        D1 = Const('D1', Data_msg)
        D2 = Const('D2', Data_msg)
        A1 = Const('A1', Ack_msg)
        A2 = Const('A2', Ack_msg)
        return And(
            ForAll(I, sym['sender_array'](I) == sym['bot']),
            ForAll(I, sym['receiver_array'](I) == sym['bot']),
            sym['sender_i'] == sym['zero_index'],
            sym['sender_gen_i'] == sym['zero_index'],
            sym['receiver_i'] == sym['zero_index'],
            sym['sender_bit']() == False,
            sym['receiver_bit']() == False,
            ForAll([D1,D2],sym['le_data_msg'](D1,D2) == False),
            ForAll([A1,A2],sym['le_ack_msg'](A1,A2) == False),
        )

    def create_transitions():

        def immutable(sym1, sym2):
            #le_index, d, dbit, abit are immutable
            I1 = Const('I1', Index)
            I2 = Const('I2', Index)
            D = Const('D1', Data_msg)
            A = Const('A1', Ack_msg)
            return And(
                ForAll([I1, I2], sym2['le_index'](I1, I2) == sym1['le_index'](I1, I2)),
                sym2['zero_index']==sym1['zero_index'],
                ForAll(D, sym2['d'](D) == sym1['d'](D)),
                ForAll(A, sym2['abit'](A) == sym1['abit'](A)),
                ForAll(D, sym2['dbit'](D) == sym1['dbit'](D)),
                sym2['bot']==sym1['bot']
            )
        
        param_gen_data = {'v':Value}
        def tr_gen_data(sym1,sym2,param):
            v = param['v']
            I = Const('I', Index)
            D1 = Const('D1', Data_msg)
            D2 = Const('D2', Data_msg)
            A1 = Const('A1', Ack_msg)
            A2 = Const('A2', Ack_msg)
            return And(
                #guard
                v != sym1['bot'],

                #transition
                immutable(sym1,sym2),
                succ_index(sym1,sym1['sender_gen_i'],sym2['sender_gen_i']),
                ForAll(I,sym2['sender_array'](I) == If(
                    I == sym1['sender_gen_i'], v, sym1['sender_array'](I)
                )),

                #everything else is unchanged 
                sym2['sender_i'] == sym1['sender_i'],
                sym2['receiver_i'] == sym1['receiver_i'],
                sym2['sender_bit']() == sym1['sender_bit'](),
                sym2['receiver_bit']() == sym1['receiver_bit'](),
                ForAll(I, sym2['receiver_array'](I) == sym1['receiver_array'](I)),
                ForAll([D1, D2], sym2['le_data_msg'](D1, D2) == sym1['le_data_msg'](D1, D2)),
                ForAll([A1, A2], sym2['le_ack_msg'](A1, A2) == sym1['le_ack_msg'](A1, A2)),

                #fairness
                sym1['sender_scheduled']()==False,
                sym1['receiver_scheduled']()==False,
                sym1['data_sent']()==False,
                sym1['data_received']()==False,
                sym1['ack_sent']()==False,
                sym1['ack_received']()==False
            )
        tr1 = ('gen_data',param_gen_data,tr_gen_data)


        def data_msg_send(sym1,sym2,m):
            D1 = Const('D1', Data_msg)
            D2 = Const('D2', Data_msg)
            return And(
                Not(sym1['le_data_msg'](m,m)),
                       ForAll([D1,D2],sym2['le_data_msg'](D1,D2)==Or(
                           sym1['le_data_msg'](D1,D2),
                           And(D1==m,D2==m),
                           And(D1==m,sym1['le_data_msg'](D2,D2))
                       ))
            )

        param_sender_send_data = {'m':Data_msg}
        def tr_sender_send_data(sym1,sym2,param):
            m = param['m']
            I = Const('I', Index)
            D1 = Const('D1', Data_msg)
            D2 = Const('D2', Data_msg)
            A1 = Const('A1', Ack_msg)
            A2 = Const('A2', Ack_msg)
            return And(
                #transition
                immutable(sym1,sym2),

                If(sym1['sender_array'](sym1['sender_i']) != sym1['bot'],
                   And(
                       #guard
                       sym1['d'](m)==sym1['sender_array'](sym1['sender_i']),
                       sym1['dbit'](m)==sym1['sender_bit'](),
                        
                       #transition
                       data_msg_send(sym1,sym2,m)
                   ),
                    ForAll([D1,D2],sym2['le_data_msg'](D1,D2)==sym1['le_data_msg'](D1,D2)),
                ),
                sym2['sender_gen_i'] == sym1['sender_gen_i'],
                sym2['sender_i'] == sym1['sender_i'],
                sym2['receiver_i'] == sym1['receiver_i'],
                sym2['sender_bit']() == sym1['sender_bit'](),
                sym2['receiver_bit']() == sym1['receiver_bit'](),
                ForAll(I, sym2['sender_array'](I) == sym1['sender_array'](I)),
                ForAll(I, sym2['receiver_array'](I) == sym1['receiver_array'](I)),
                ForAll([A1, A2], sym2['le_ack_msg'](A1, A2) == sym1['le_ack_msg'](A1, A2)),

                #fairness
                sym1['sender_scheduled']()==True,
                sym1['receiver_scheduled']()==False,
                sym1['data_sent']()==(sym1['sender_array'](sym1['sender_i']) != sym1['bot']),
                sym1['data_received']()==False,
                sym1['ack_sent']()==False,
                sym1['ack_received']()==False
            )
        tr2 = ('sender_send_data',param_sender_send_data,tr_sender_send_data)

        def ack_msg_receive(sym1,sym2,a):
            A1 = Const('A1', Ack_msg)
            A2 = Const('A2', Ack_msg)
            return And(
                sym1['le_ack_msg'](a,a),
                ForAll(A1,Implies(sym1['le_ack_msg'](a,A1),a==A1)),
                ForAll([A1,A2],sym2['le_ack_msg'](A1,A2)==And(
                    sym1['le_ack_msg'](A1,A2),
                    A2!=a
                ))
            )
        
        param_sender_receive_ack = {'a':Ack_msg}
        def tr_sender_receive_ack(sym1,sym2,param):
            a = param['a']
            I = Const('I', Index)
            D1 = Const('D1', Data_msg)
            D2 = Const('D2', Data_msg)
            return And(
                #transition
                immutable(sym1,sym2),
                
                ack_msg_receive(sym1,sym2,a),
                If(sym1['abit'](a)==sym1['sender_bit'](),
                   And(
                       sym2['sender_bit']()==Not(sym1['sender_bit']()),
                       succ_index(sym1,sym1['sender_i'],sym2['sender_i'])
                   ),
                   And(
                        sym2['sender_bit']()==sym1['sender_bit'](),
                        sym2['sender_i']==sym1['sender_i']
                   )
                ),
                sym2['sender_gen_i'] == sym1['sender_gen_i'],
                sym2['receiver_i'] == sym1['receiver_i'],
                ForAll(I, sym2['sender_array'](I) == sym1['sender_array'](I)),
                ForAll(I, sym2['receiver_array'](I) == sym1['receiver_array'](I)),
                ForAll([D1, D2], sym2['le_data_msg'](D1, D2) == sym1['le_data_msg'](D1, D2)),
                sym2['receiver_bit']() == sym1['receiver_bit'](),

                #fairness
                sym1['sender_scheduled']()==False,
                sym1['receiver_scheduled']()==False,
                sym1['data_sent']()==False,
                sym1['data_received']()==True,
                sym1['ack_sent']()==False,
                sym1['ack_received']()==False
            )
        tr3 = ('sender_receive_ack',param_sender_receive_ack,tr_sender_receive_ack)

        def data_msg_receive(sym1,sym2,m):
            D1 = Const('D1', Data_msg)
            D2 = Const('D2', Data_msg)
            return And(
                sym1['le_data_msg'](m,m),
                ForAll(D1,Implies(sym1['le_data_msg'](m,D1),m==D1)),
                ForAll([D1,D2],sym2['le_data_msg'](D1,D2)==And(
                    sym1['le_data_msg'](D1,D2),
                    D2!=m
                ))
            )

        param_receiver_receive_data = {'m':Data_msg}
        def tr_receiver_receive_data(sym1,sym2,param):
            m = param['m']
            I = Const('I', Index)
            A1 = Const('A1', Ack_msg)
            A2 = Const('A2', Ack_msg)
            return And(
                #transition
                immutable(sym1,sym2),
                
                data_msg_receive(sym1,sym2,m),
                If(
                    sym1['dbit'](m)==sym1['receiver_bit'](),
                    And(
                        sym2['receiver_bit']()==Not(sym1['receiver_bit']()),
                        ForAll(I,sym2['receiver_array'](I)==If(
                            I==sym1['receiver_i'],sym1['d'](m),sym1['receiver_array'](I)
                        )),
                        succ_index(sym1,sym1['receiver_i'],sym2['receiver_i'])
                    ),
                    And(
                        sym2['receiver_bit']()==sym1['receiver_bit'](),
                        ForAll(I,sym2['receiver_array'](I)==sym1['receiver_array'](I)),
                        sym2['receiver_i']==sym1['receiver_i']
                    )
                ),
                sym2['sender_gen_i'] == sym1['sender_gen_i'],
                sym2['sender_i'] == sym1['sender_i'],
                ForAll(I, sym2['sender_array'](I) == sym1['sender_array'](I)),
                ForAll([A1, A2], sym2['le_ack_msg'](A1, A2) == sym1['le_ack_msg'](A1, A2)),
                sym2['sender_bit']()==sym1['sender_bit'](),

                #fairness
                sym1['sender_scheduled']()==False,
                sym1['receiver_scheduled']()==False,
                sym1['data_sent']()==False,
                sym1['data_received']()==True,
                sym1['ack_sent']()==False,
                sym1['ack_received']()==False
            )
        tr4 = ('receiver_receive_data',param_receiver_receive_data,tr_receiver_receive_data)
        
        def ack_msg_send(sym1,sym2,a):
            A1 = Const('A1', Ack_msg)
            A2 = Const('A2', Ack_msg)
            return And(
                Not(sym1['le_ack_msg'](a,a)),
                ForAll([A1,A2],sym2['le_ack_msg'](A1,A2)==Or(
                    sym1['le_ack_msg'](A1,A2),
                    And(A1==a,A2==a),
                    And(A1==a,sym1['le_ack_msg'](A2,A2))
                    ))
            )

        param_receiver_send_ack = {'a':Ack_msg}
        def tr_receiver_send_ack(sym1,sym2,param):
            a = param['a']
            I = Const('I', Index)
            D1 = Const('D1', Data_msg)
            D2 = Const('D2', Data_msg)
            return And(
                #transition
                immutable(sym1,sym2),
                
                sym1['abit'](a)==Not(sym1['receiver_bit']()),
                ack_msg_send(sym1,sym2,a),

                sym2['sender_gen_i'] == sym1['sender_gen_i'],
                sym2['sender_i'] == sym1['sender_i'],
                sym2['receiver_i'] == sym1['receiver_i'],
                sym2['sender_bit']() == sym1['sender_bit'](),
                sym2['receiver_bit']() == sym1['receiver_bit'](),
                ForAll(I, sym2['sender_array'](I) == sym1['sender_array'](I)),
                ForAll(I, sym2['receiver_array'](I) == sym1['receiver_array'](I)),
                ForAll([D1, D2], sym2['le_data_msg'](D1, D2) == sym1['le_data_msg'](D1, D2)),

                #fairness
                sym1['sender_scheduled']()==False,
                sym1['receiver_scheduled']()==True,
                sym1['data_sent']()==False,
                sym1['data_received']()==False,
                sym1['ack_sent']()==True,
                sym1['ack_received']()==False
            )
        tr5 = ('receiver_send_ack',param_receiver_send_ack,tr_receiver_send_ack)

        param_data_msg_drop = {'m': Data_msg}
        def tr_data_msg_drop(sym1, sym2, param):
            m = param['m']
            D1 = Const('D1', Data_msg)
            D2 = Const('D2', Data_msg)
            A1 = Const('A1',Ack_msg)
            A2 = Const('A2',Ack_msg)
            I = Const('I',Index)
            return And(
            # transition
            immutable(sym1, sym2),
            ForAll([D1, D2], sym2['le_data_msg'](D1, D2) == And(
                sym1['le_data_msg'](D1, D2),
                D1 != m,
                D2 != m
            )),
            sym2['sender_gen_i'] == sym1['sender_gen_i'],
            sym2['sender_i'] == sym1['sender_i'],
            sym2['receiver_i'] == sym1['receiver_i'],
            sym2['sender_bit']() == sym1['sender_bit'](),
            sym2['receiver_bit']() == sym1['receiver_bit'](),
            ForAll(I, sym2['sender_array'](I) == sym1['sender_array'](I)),
            ForAll(I, sym2['receiver_array'](I) == sym1['receiver_array'](I)),
            ForAll([A1, A2], sym2['le_ack_msg'](A1, A2) == sym1['le_ack_msg'](A1, A2)),

            # fairness
            sym1['sender_scheduled']() == False,
            sym1['receiver_scheduled']() == False,
            sym1['data_sent']() == False,
            sym1['data_received']() == False,
            sym1['ack_sent']() == False,
            sym1['ack_received']() == False
            )
        tr6 = ('data_msg_drop', param_data_msg_drop, tr_data_msg_drop)

        param_ack_msg_drop = {'a': Ack_msg}
        def tr_ack_msg_drop(sym1, sym2, param):
            a = param['a']
            D1 = Const('D1', Data_msg)
            D2 = Const('D2', Data_msg)
            A1 = Const('A1',Ack_msg)
            A2 = Const('A2',Ack_msg)
            I = Const('I',Index)
            return And(
            # transition
            immutable(sym1, sym2),
            ForAll([A1, A2], sym2['le_ack_msg'](A1, A2) == And(
                sym1['le_ack_msg'](A1, A2),
                A1 != a,
                A2 != a
            )),
            sym2['sender_gen_i'] == sym1['sender_gen_i'],
            sym2['sender_i'] == sym1['sender_i'],
            sym2['receiver_i'] == sym1['receiver_i'],
            sym2['sender_bit']() == sym1['sender_bit'](),
            sym2['receiver_bit']() == sym1['receiver_bit'](),
            ForAll(I, sym2['sender_array'](I) == sym1['sender_array'](I)),
            ForAll(I, sym2['receiver_array'](I) == sym1['receiver_array'](I)),
            ForAll([D1, D2], sym2['le_data_msg'](D1, D2) == sym1['le_data_msg'](D1, D2)),

            # fairness
            sym1['sender_scheduled']() == False,
            sym1['receiver_scheduled']() == False,
            sym1['data_sent']() == False,
            sym1['data_received']() == False,
            sym1['ack_sent']() == False,
            sym1['ack_received']() == False
            )
        tr7 = ('ack_msg_drop', param_ack_msg_drop, tr_ack_msg_drop)
        
        return [tr1,tr2,tr3,tr5,tr6,tr7]

    ts = TS(sorts,axiom,init,create_transitions(),constant_sym,relation_sym,function_sym)
    return ts

ts = create_ts()

# bounded model checking
true = lambda *args : True
# ts.bounded_check([true,true]) 

#currently invariant doesn't work 
def system_invariant(sym):
    I = Const('I', Index)
    M = Const('M', Data_msg)
    M1 = Const('M1', Data_msg)
    M2 = Const('M2', Data_msg)
    M3 = Const('M3', Data_msg)
    A = Const('A', Ack_msg)
    A1 = Const('A1', Ack_msg)
    A2 = Const('A2', Ack_msg)
    A3 = Const('A3', Ack_msg)

    return And(
    # invariant le(X, Y) & le(Y, Z) -> le(X, Z)  # Transitivity
    # invariant le(X, Y) & le(Y, X) -> X = Y  # Anti-symmetry
    # invariant le(X, Y) -> le(X, X) & le(Y, Y)  # Partial reflexivity
    # invariant le(X, X) & le(Y, Y) -> le(X, Y) | le(Y, X)  # Partial Totality
    ForAll([M1, M2, M3], Implies(And(sym['le_data_msg'](M1, M2), sym['le_data_msg'](M2, M3)), sym['le_data_msg'](M1, M3))),
    ForAll([M1, M2], Implies(And(sym['le_data_msg'](M1, M2), sym['le_data_msg'](M2, M1)), M1 == M2)),
    ForAll([M1, M2], Implies(sym['le_data_msg'](M1, M2), And(sym['le_data_msg'](M1, M1), sym['le_data_msg'](M2, M2)))),
    ForAll([M1, M2], Implies(And(sym['le_data_msg'](M1, M1), sym['le_data_msg'](M2, M2)), Or(sym['le_data_msg'](M1, M2), sym['le_data_msg'](M2, M1)))),
    
    ForAll([A1, A2, A3], Implies(And(sym['le_ack_msg'](A1, A2), sym['le_ack_msg'](A2, A3)), sym['le_ack_msg'](A1, A3))),
    ForAll([A1, A2], Implies(And(sym['le_ack_msg'](A1, A2), sym['le_ack_msg'](A2, A1)), A1 == A2)),
    ForAll([A1, A2], Implies(sym['le_ack_msg'](A1, A2), And(sym['le_ack_msg'](A1, A1), sym['le_ack_msg'](A2, A2)))),
    ForAll([A1, A2], Implies(And(sym['le_ack_msg'](A1, A1), sym['le_ack_msg'](A2, A2)), Or(sym['le_ack_msg'](A1, A2), sym['le_ack_msg'](A2, A1)))),

    
    # invariant index.le(sender_gen_i, I) <-> sender_array(I) = bot
    # invariant index.le(receiver_i, I) <-> receiver_array(I) = bot
    # invariant index.le(sender_i, sender_gen_i)
    ForAll(I, sym['le_index'](sym['sender_gen_i'], I) == (sym['sender_array'](I) == sym['bot'])),
    ForAll(I, sym['le_index'](sym['receiver_i'], I) == (sym['receiver_array'](I) == sym['bot'])),
    sym['le_index'](sym['sender_i'], sym['sender_gen_i']),
    
    # invariant ~sender_bit & ~receiver_bit & ack_msg.le(A,A) -> abit(A)
    # invariant ~sender_bit & ~receiver_bit & data_msg.le(M1,M2) -> ~(dbit(M1) & ~dbit(M2))
    ForAll(A, Implies(And(Not(sym['sender_bit']()), Not(sym['receiver_bit']()), sym['le_ack_msg'](A, A)), sym['abit'](A))),
    ForAll([M1, M2], Implies(
        And(Not(sym['sender_bit']()), Not(sym['receiver_bit']()), sym['le_data_msg'](M1, M2)),
        Not(And(sym['dbit'](M1), Not(sym['dbit'](M2))))
    )),
    
    # invariant sender_bit & receiver_bit & ack_msg.le(A,A) -> ~abit(A)
    # invariant sender_bit & receiver_bit & data_msg.le(M1,M2) -> ~(~dbit(M1) & dbit(M2))
    ForAll(A, Implies(And(sym['sender_bit'](), sym['receiver_bit'](), sym['le_ack_msg'](A, A)), Not(sym['abit'](A)))),
    ForAll([M1, M2], Implies(
        And(sym['sender_bit'](), sym['receiver_bit'](), sym['le_data_msg'](M1, M2)),
        Not(And(Not(sym['dbit'](M1)), sym['dbit'](M2)))
    )),
    
    # invariant ~sender_bit & receiver_bit & data_msg.le(M,M) -> ~dbit(M)
    # invariant ~sender_bit & receiver_bit & ack_msg.le(A1,A2) -> ~(abit(A1) & ~abit(A2))
    ForAll(M, Implies(And(Not(sym['sender_bit']()), sym['receiver_bit'](), sym['le_data_msg'](M, M)), Not(sym['dbit'](M)))),
    ForAll([A1, A2], Implies(And(Not(sym['sender_bit']()), sym['receiver_bit'](), sym['le_ack_msg'](A1, A2)), Not(And(sym['abit'](A1), Not(sym['abit'](A2)))))),
    
    # invariant sender_bit & ~receiver_bit & data_msg.le(M,M) -> dbit(M)
    # invariant sender_bit & ~receiver_bit & ack_msg.le(A1,A2) -> ~(~abit(A1) & abit(A2))
    ForAll(M, Implies(And(sym['sender_bit'](), Not(sym['receiver_bit']()), sym['le_data_msg'](M, M)), sym['dbit'](M))),
    ForAll([A1, A2], Implies(And(sym['sender_bit'](), Not(sym['receiver_bit']()), sym['le_ack_msg'](A1, A2)), Not(And(Not(sym['abit'](A1)), sym['abit'](A2))))),
    
    # invariant (sender_bit <-> receiver_bit)  -> sender_i = receiver_i
    Implies(sym['sender_bit']() == sym['receiver_bit'](), sym['sender_i'] == sym['receiver_i']),
    
    # invariant (sender_bit <-> ~receiver_bit) -> (
    #     # receiver_i = sender_i + 1
    #     ~index.le(receiver_i, sender_i) &
    #     (forall I. ~index.le(I,sender_i) -> index.le(receiver_i,I))
    # )
    Implies(sym['sender_bit']() != sym['receiver_bit'](), And(
        Not(sym['le_index'](sym['receiver_i'], sym['sender_i'])),
        ForAll(I, Implies(Not(sym['le_index'](I, sym['sender_i'])), sym['le_index'](sym['receiver_i'], I)))
    )),
    
    # invariant data_msg.le(M,M) & (dbit(M) <-> sender_bit) -> ~index.le(sender_gen_i, sender_i)
    ForAll(M, Implies(And(sym['le_data_msg'](M, M), sym['dbit'](M) == sym['sender_bit']()), Not(sym['le_index'](sym['sender_gen_i'], sym['sender_i'])))),
    
    # invariant data_msg.le(M,M) & (dbit(M) <-> sender_bit) -> d(M) = sender_array(sender_i)
    ForAll(M, Implies(And(sym['le_data_msg'](M, M), sym['dbit'](M) == sym['sender_bit']()), sym['d'](M) == sym['sender_array'](sym['sender_i']))),
    
    # invariant data_msg.le(M,M) -> d(M) ~= bot
    ForAll(M, Implies(sym['le_data_msg'](M, M), sym['d'](M) != sym['bot'])),
    
    # invariant ack_msg.le(A,A) & (abit(A) <-> sender_bit) -> ~index.le(receiver_i,sender_i)
    ForAll(A, Implies(And(sym['le_ack_msg'](A, A), sym['abit'](A) == sym['sender_bit']()), Not(sym['le_index'](sym['receiver_i'], sym['sender_i'])))),
    
    # invariant ack_msg.le(A,A) & (abit(A) <-> sender_bit) -> receiver_array(sender_i) = sender_array(sender_i)
    ForAll(A, Implies(And(sym['le_ack_msg'](A, A), sym['abit'](A) == sym['sender_bit']()), sym['receiver_array'](sym['sender_i']) == sym['sender_array'](sym['sender_i']))),
    
    # invariant ack_msg.le(A,A) & (abit(A) <-> sender_bit) -> receiver_array(sender_i) ~= bot
    ForAll(A, Implies(And(sym['le_ack_msg'](A, A), sym['abit'](A) == sym['sender_bit']()), sym['receiver_array'](sym['sender_i']) != sym['bot'])),
    
    # safety - receiver array has values from sender array for all received indices
    # invariant receiver_array(I) ~= bot -> receiver_array(I) = sender_array(I)
    ForAll(I, Implies(sym['receiver_array'](I) != sym['bot'], sym['receiver_array'](I) == sym['sender_array'](I))),
    )

# ts.check_inductiveness(system_invariant)

#temporal property - negated and skolemized

sender_scheduled = Function('sender_scheduled', BoolSort())
receiver_scheduled = Function('receiver_scheduled', BoolSort())
data_sent = Function('data_sent', BoolSort())
data_received = Function('data_received', BoolSort())
ack_sent = Function('ack_sent', BoolSort())
ack_received = Function('ack_received', BoolSort())
sender_array = Function('sender_array', Index, Value)
receiver_array = Function('receiver_array', Index, Value)
sk_index = Const('sk_index', Index)
bot = Const('bot',Value)

formula = foltl_nnf(
    And(
        G(F(sender_scheduled())),
        G(F(receiver_scheduled())),
        Implies(G(F(data_sent())),G(F(data_received()))),
        Implies(G(F(ack_sent())),G(F(ack_received()))),
        F(sender_array(sk_index)!=bot),
        G(receiver_array(sk_index)==bot)
    )
)

timer_system = timer_transition_system(formula,{'sk_index':Index,'bot':Value})
intersection = IntersectionTS(ts, timer_system)

#timer invariant

def timer_invariant(sym):
    return And(
    )

def invariant(sym):
    return And(
        system_invariant(sym),
        timer_invariant(sym)
    )

#rank

rank = BinaryFreeRank(lambda *args: True)

proof = TerminationProof(rank,invariant)
proof.check_proof(intersection)
