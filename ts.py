from z3 import *
from typing import Dict, Callable, Tuple, List
import itertools

#Currently have 4 permutation classes - need to choose which ones we want to keep

true = lambda sym: z3.BoolVal(True)

def sat_check(constraints: List[z3.BoolRef], 
              find_model = True, 
              minimize_model = True, 
              unsat_core = False,
              print_calls = False,
              minimize_sorts: list[z3.z3.SortRef] = []) -> Tuple[z3.CheckSatResult, z3.ModelRef]:
    z3.set_param('timeout', 5*60*1000) #5 minute timeout
    solver = Solver()
    solver.set(mbqi=True)
    # Enable unsat core tracking
    if unsat_core:
        solver.set(unsat_core=True)
        i = 0
        for c in constraints:
            if print_calls:
                print('constraint number',i)
                print(c)
            solver.assert_and_track(c,str(i))
            i = i+1
    else:
        for c in constraints:
            solver.add(c)
            if print_calls:
                print(c)

    #print(solver.sexpr()) #printing to smtlib

    result=solver.check()
    if result == z3.unsat:
        if unsat_core:
            core = solver.unsat_core()
            print("Unsat core:", core)
    if result == z3.sat: 
        if find_model==True:
            model = None
            if minimize_model==True:
                m = 1
                while m<8 and model == None: #Currently this just naively checks if there's a model with m of each sort
                    solver.push()
                    for i in range(len(minimize_sorts)): 
                        size_const = size_constraint(minimize_sorts[i],m)
                        solver.add(size_const)
                    new_result = solver.check()
                    if new_result == z3.sat:
                        print("small model of size: ",m)
                        model = solver.model()
                        break 
                    else: 
                        solver.pop()
                    m = m + 1
                    
            if model == None:
                print("small model failed")
                #In all sizes up to the bound we don't have a model - so we just output any model
                try:
                    model = solver.model()
                except z3.Z3Exception as e:
                    print("sat but no model")
                    return (z3.sat,None)
            return (z3.sat,model)
    else: 
        return (result,None)

def print_model_in_order(model,symbols):
    sorts = model.sorts()
    for s in sorts:
        print(model.get_universe(s))
    try:
        for symbol in symbols:
            print(symbol, ":", model[symbol])
    except Exception as e:
        print("A KeyError occurred:", e)
        print(model)

def size_constraint(sort,m):
    new_variables = [Const('size'+str(sort)+str(i),sort) for i in range(m)]
    any = Const('any',sort)
    new_constraints = [(any == new_variables[i]) for i in range(m)]
    return ForAll(any,Or(new_constraints))

##Helper functions::

def create_variable(var_sort,var_name):
    if var_sort == IntSort():
        return Int(var_name)
    return Const(var_name,var_sort)

def create_function(func_sorts,func_name):
    return Function(func_name,*func_sorts)

def create_relation(rel_sorts,rel_name):
    return create_function(rel_sorts+[BoolSort()],rel_name)

def add_exists(formula,formula_param):
    sort_dict = formula_param
    var_dict = create_dictionary_of_variables(sort_dict)
    new_variables = list(var_dict.values())
    if new_variables:
        new_quantified_formula = lambda sym1, sym2, formula=formula, new_variables=new_variables: Exists(new_variables, formula(sym1, sym2, var_dict))
    else:
        new_quantified_formula = lambda sym1, sym2, formula=formula: formula(sym1, sym2, var_dict)
    return new_quantified_formula
    #something weird happened here with the lambda, and chatgpt suggested adding the transition=transition, and the new_vaiables=new_variables
    #Maybe we can remove it at this point
    #This only works if its sym1,sym2 :( 

def create_dictionary_of_variables(sort_dict,suffix=''):
    #Takes a dictionary of name->sort and returns a dictionary of name->z3.var
    var_names = list(sort_dict.keys())
    var_dict = {}
    for i in range(len(var_names)):
        var_name = var_names[i]
        new_var = create_variable(sort_dict[var_name],var_name+suffix)   
        var_dict[var_name] = new_var
    return var_dict

def equality_dicts(var_dict1,var_dict2):
    #checks whether two dictionaries of variables are equal
    #importantly - we only compare the values for keys that
    #appear in var_dict1, so it is actually more of a subset check
    var_names = list(var_dict1.keys())
    res = And([var_dict1[name]==var_dict2[name] for name in var_names])
    return res

def list_dict_product(list1,list2):
    return [ dict1 | dict2 for dict1 in list1 for dict2 in list2]

"""
def minimality_axiom(sort,predicate,order):
    X = create_variable(sort,'X')
    Xmin = create_variable(sort,'Xmin')
    Y = create_variable(sort,'Y')
    return Implies(
            Exists(X,predicate(X)),
            Exists(Xmin,And(predicate(Xmin),
                         ForAll(Y,Implies(order(Y,Xmin),Not(predicate(Y)))))))

def maximality_axiom(sort,predicate,order):
    X = create_variable(sort,'X')
    Xmax = create_variable(sort,'Xmax')
    Y = create_variable(sort,'Y')
    return Implies(
            Exists(X,predicate(X)),
            Exists(Xmax,And(predicate(Xmax),
                         ForAll(Y,Implies(order(Xmax,Y),Not(predicate(Y)))))))
"""

#A class that defines a single state (structure)
class State:
    def __init__(self,sorts:list,constant_sym:dict,relation_sym:dict,function_sym:dict,name:str) -> None:
        self.sorts=sorts
        self.name=name
        self.constant_sym=constant_sym
        self.function_sym=function_sym
        self.relation_sym=relation_sym
        self.dict={}
        self.create_sym()

    def create_sym(self) -> None:
        for const_name,const_sort in self.constant_sym.items():
            self.dict[const_name]=create_variable(const_sort,const_name+self.name)
        for rel_name,rel_sort in self.relation_sym.items():
            self.dict[rel_name]=create_relation(rel_sort,rel_name+self.name)
        for func_name,func_sorts in self.function_sym.items():
            self.dict[func_name]=create_function(func_sorts,func_name+self.name)

    def get_dict(self):
        return self.dict
    
    def get_sym(self):
        return list(self.dict.values())
    
#A class that defines a transition system
class TS:
    def __init__(self,sorts:list,axiom = true ,init = true ,transitions:list = [], constant_sym:dict={}, relation_sym:dict={}, function_sym:dict={} ):
        self.sorts=sorts
        self.axiom=axiom
        self.init=init
        self.transitions=transitions #list of transitions: name, free variables, and formula with the free variables - the first element is always idle
        self.tr=self.create_tr()
        self.constant_sym=constant_sym
        self.relation_sym=relation_sym
        self.function_sym=function_sym

    def create_tr(self):
        #takes the list of transitions and returns the formula tr which is of the form Or(exists(x)tr1(x),exists(x)tr2(x)..) as a function on symbols dictionaries.
        quantified_transitions=[]
        for transition in self.transitions:
            new_quan_trans = add_exists(transition[2],transition[1])
            quantified_transitions.append(new_quan_trans)
        return lambda sym1,sym2 : Or( [f(sym1,sym2) for f in quantified_transitions] ) 

    def create_state(self,name):
        state = State(self.sorts,self.constant_sym,self.relation_sym,self.function_sym,name)
        return state
    
    def ts_sat_check(self,constraints,states):
        #Calls the sat_check, adds the axioms constraints on all states
        minimize_sorts = self.sorts
        axiom_constraints=[]
        for state in states:
            new_axiom_constraint=self.axiom(state.get_dict())
            axiom_constraints.append(new_axiom_constraint)
        constraints = constraints + axiom_constraints
        return sat_check(constraints,minimize_sorts=minimize_sorts) #HERE YOU CAN CHANGE THE PRINTS

    def bounded_check(self,formulas: list):
        #State 0 satis. init and each pair i,i+1 satis. tr
        #Could potentially add the specific transitions like in mypyvy
        n = len(formulas)
        states = []
        constraints = []
        symbols=[]
        state0 = self.create_state(str(0))
        states.append(state0)
        symbols=symbols+list(state0.get_dict().values())
        constraints.append(self.init(state0.get_dict()))
        constraints.append(formulas[0](state0.get_dict()))
        for i in range(1,n):
            statei=self.create_state(str(i))
            states.append(statei)
            symbols=symbols+list(statei.get_dict().values())
            constraints.append((formulas[i](states[i].get_dict())))
            constraints.append(self.tr(states[i-1].get_dict(),states[i].get_dict()))
        sat_result = self.ts_sat_check(constraints,states)           
        print("bounded check result: ",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],symbols)
            #print(sat_result[1])

    def check_inductiveness(self,inv):
        res_init=self.check_init_maintains_inv(inv)
        res_tr=self.check_tr_maintains_inv(inv)
        return res_init and res_tr

    def check_init_maintains_inv(self,inv):
        state_init = self.create_state("_init")
        states=[state_init]
        constraint1=self.init(state_init.get_dict())
        constraint2=Not(inv(state_init.get_dict()))
        constraints=[constraint1,constraint2]
        sat_result = self.ts_sat_check(constraints,states)
        print("init -> inv result:",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],state_init.get_sym())     
        return (sat_result[0] == z3.unsat)
    
    def check_tr_maintains_inv(self,inv):
        state_pre = self.create_state("_pre")
        state_post = self.create_state("_post")
        states=[state_pre,state_post]
        constraint1=inv(state_pre.get_dict())
        constraint2=self.tr(state_pre.get_dict(),state_post.get_dict()) 
        constraint3=Not(inv(state_post.get_dict()))
        constraints=[constraint1,constraint2,constraint3]
        sat_result = self.ts_sat_check(constraints,states)
        print("inv & tr -> inv result:",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],state_pre.get_sym()+state_post.get_sym())     
        return (sat_result[0] == z3.unsat)
    
    def check_tr_maintains_axiom(self):
        axiom = self.axiom
        state_pre = self.create_state("_pre")
        state_post = self.create_state("_post")
        states=[state_pre,state_post] #we do not give the states to the solver, because we do not want it to add the axioms!
        constraint1=axiom(state_pre.get_dict())
        constraint2=self.tr(state_pre.get_dict(),state_post.get_dict()) 
        constraint3=Not(axiom(state_post.get_dict()))
        constraints=[constraint1,constraint2,constraint3]
        sat_result = self.ts_sat_check(constraints,[])
        print("axiom & tr -> axiom result:",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],state_pre.get_sym()+state_post.get_sym())     
        return sat_result


##In these implementations 'FreeRank' has free variables param1,param2 for pre state and post state free variables
##In all functions they should have default value {}, because in the end we want to generate a closed implicit ranking.
##If free variables still exist in the formula used in the final rank, there will be an error.
##We have an implementation of equality of the rank as well, but we probably will not use it.

class FreeRank:
    #in this class equal,reduced,conserved take sym1,sym2,param1={},param2={}
    def __init__(self,equal,reduced,conserved,param={}):
        self.equal = equal 
        self.reduced = reduced
        self.conserved = conserved
        self.param = param
            
    def create_conserved(self):
        def res(sym1,sym2,param1={},param2={}):
            return Or(self.equal(sym1,sym2,param1,param2),self.reduced(sym1,sym2,param1,param2))
        return res
    
    def print_reduced(self,ts):
        state0 = ts.create_state('0')
        state1 = ts.create_state('1')
        var_dict0 = create_dictionary_of_variables(self.param,'0')
        var_dict1 = create_dictionary_of_variables(self.param,'1')
        print(self.reduced(state0.get_dict(),state1.get_dict(),var_dict0,var_dict1))

    def print_conserved(self,ts):
        state0 = ts.create_state('0')
        state1 = ts.create_state('1')
        var_dict0 = create_dictionary_of_variables(self.param,'0')
        var_dict1 = create_dictionary_of_variables(self.param,'1')
        print(self.conserved(state0.get_dict(),state1.get_dict(),var_dict0,var_dict1))

    def print_equal(self,ts):
        state0 = ts.create_state('0')
        state1 = ts.create_state('1')
        var_dict0 = create_dictionary_of_variables(self.param,'0')
        var_dict1 = create_dictionary_of_variables(self.param,'1')
        print(self.equal(state0.get_dict(),state1.get_dict(),var_dict0,var_dict1))

    def print_structure(self):
        print('user_provided')

class BinaryFreeRank(FreeRank):
    #This class generates formulas with different free variables for the pre and post states.
    def __init__(self,predicate,param={}):
        #predicate is a function predicate(sym,param)
        self.predicate = predicate
        self.param = param
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()
    
    def create_equal(self):
        pred = self.predicate
        def res(sym1,sym2,param1={},param2={}):
            return pred(sym1,param1)==pred(sym2,param2)
        return res
        
    def create_reduced(self):
        pred = self.predicate
        def res(sym1,sym2,param1={},param2={}):
            return And(pred(sym1,param1),Not(pred(sym2,param2)))
        return res

    def create_conserved(self):
        pred = self.predicate
        def res(sym1,sym2,param1={},param2={}):
            return Implies(pred(sym2,param2),pred(sym1,param1))
        return res
    
    def print_structure(self):
        print('Bin',end='')

class PointwiseFreeRank(FreeRank):
    def __init__(self,ranks:list[FreeRank],param={}):
        self.param = param
        self.ranks = ranks
        self.equal = self.create_equal() 
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()
    
    def create_equal(self):
        ranks = self.ranks
        equalities = [rank.equal for rank in ranks]
        def res(sym1,sym2,param1={},param2={}):
            return And([equal(sym1,sym2,param1,param2) for equal in equalities])
        return res
    
    def create_conserved(self):
        ranks = self.ranks
        conserveds = [rank.conserved for rank in ranks]
        def res(sym1,sym2,param1={},param2={}):
            return And([conserved(sym1,sym2,param1,param2) for conserved in conserveds])
        return res
    
    def create_reduced(self):
        ranks = self.ranks
        conserveds = [rank.conserved for rank in ranks]
        reduceds = [rank.reduced for rank in ranks]
        def res(sym1,sym2,param1={},param2={}):
            return And(
                And([conserved(sym1,sym2,param1,param2) for conserved in conserveds]),
                Or([reduced(sym1,sym2,param1,param2) for reduced in reduceds]))
        return res
    
    def print_structure(self):
        ranks = self.ranks
        print('PW(',end='')
        for rank in ranks:
            rank.print_structure()
            print(',',end='')
        print(')',end='')

class LexFreeRank(FreeRank):
    def __init__(self,ranks:list[FreeRank],param={}):
        self.param = param
        self.ranks = ranks
        self.equal = self.create_equal() 
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()
    
    def create_equal(self):
        ranks = self.ranks
        equalities = [rank.equal for rank in ranks]
        def res(sym1,sym2,param1={},param2={}):
            return And([equal(sym1,sym2,param1,param2) for equal in equalities])
        return res
    
    def create_conserved(self):
        ranks = self.ranks
        conserveds = [rank.conserved for rank in ranks]
        reduced = self.reduced
        def res(sym1,sym2,param1={},param2={}):
            return Or(
                And([conserved(sym1,sym2,param1,param2) for conserved in conserveds]),
                reduced(sym1,sym2,param1,param2)
            )
        return res
    
    def create_reduced(self):
        ranks = self.ranks
        conserveds = [rank.conserved for rank in ranks]
        reduceds = [rank.reduced for rank in ranks]
        reduced_i_and_conserved_belows = []
        for i in range(len(ranks)):
            def reduced_i_conserved_below(sym1,sym2,param1={},param2={},i=i):
                return And(reduceds[i](sym1,sym2,param1,param2),And([conserveds[j](sym1,sym2,param1,param2) for j in range(i)]))
            reduced_i_and_conserved_belows.append(reduced_i_conserved_below)
        def res(sym1,sym2,param1={},param2={}):
            return And(
                Or([formula(sym1,sym2,param1,param2) for formula in reduced_i_and_conserved_belows]))
        return res
    
    def print_structure(self):
        ranks = self.ranks
        print('Lex(',end='')
        for rank in ranks:
            rank.print_structure()
            print(',',end='')
        print(')',end='')

class LinFreeRank(FreeRank):
    def __init__(self,ranks:list[FreeRank],conditions,param={}):
        self.param = param
        self.ranks = ranks
        self.conditions = conditions
        self.disjoint_conds = self.create_disjoint_conds()
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()

    def create_disjoint_conds(self):
        conditions = self.conditions
        n = len(conditions)
        disj_conds = []
        for i in range(n):
            func_i = lambda sym,param,i=i: And(conditions[i](sym,param),
                           And([Not(conditions[j](sym,param)) for j in range(i)]))
            disj_conds.append(func_i)
        return disj_conds

    def create_equal(self):
        ranks = self.ranks 
        equalities = [rank.equal for rank in ranks]
        disjoint_conds = self.disjoint_conds
        n = len(ranks)
        equality = lambda sym1,sym2,param1={},param2={}: Or([And(equalities[i](sym1,sym2,param1,param2),disjoint_conds[i](sym1,param1),disjoint_conds[i](sym2,param2)) for i in range(n)])
        return equality

    def create_reduced(self):
        ranks = self.ranks 
        reduceds = [rank.reduced for rank in ranks]
        disjoint_conds = self.disjoint_conds
        n = len(ranks)
    
        reduced_in_same_comps = lambda sym1,sym2,param1={},param2={}: Or([And(reduceds[i](sym1,sym2,param1,param2),
                                                                        disjoint_conds[i](sym1,param1),
                                                                        disjoint_conds[i](sym2,param2)) for i in range(n)])

        pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
        reduced_in_diff_comps = lambda sym1,sym2,param1={},param2={}: Or([And(disjoint_conds[i](sym1,param1),
                                                                        disjoint_conds[j](sym2,param2)) for (i,j) in pairs])
        return lambda sym1,sym2,param1={},param2={} : Or(reduced_in_same_comps(sym1,sym2,param1,param2),
                                                   reduced_in_diff_comps(sym1,sym2,param1,param2))

    def create_conserved(self):
        ranks = self.ranks 
        conserveds = [rank.conserved for rank in ranks]
        disjoint_conds = self.disjoint_conds
        n = len(ranks)
    
        conserved_in_same_comps = lambda sym1,sym2,param1={},param2={}: Or([And(conserveds[i](sym1,sym2,param1,param2),
                                                                        disjoint_conds[i](sym1,param1),
                                                                        disjoint_conds[i](sym2,param2)) for i in range(n)])

        pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
        reduced_in_diff_comps = lambda sym1,sym2,param1={},param2={}: Or([And(disjoint_conds[i](sym1,param1),
                                                                        disjoint_conds[j](sym2,param2)) for (i,j) in pairs])
        return lambda sym1,sym2,param1={},param2={} : Or(conserved_in_same_comps(sym1,sym2,param1,param2),
                                                   reduced_in_diff_comps(sym1,sym2,param1,param2))

    def print_structure(self):
        ranks = self.ranks
        print('+(',end='')
        for rank in ranks:
            rank.print_structure()
            print(',',end='')
        print(')',end='')

class SubstFreeRank(FreeRank):
    def __init__(self,base_rank,param_subst : dict,terms_subst : dict,param={}):
        self.base_rank = base_rank
        self.param_subst = param_subst 
        self.terms_subst = terms_subst 
        self.param = param
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()
        
    def create_any(self,formula):
        terms_subst = self.terms_subst
        def res(sym1,sym2,param1={},param2={}):
            terms_subst_inst1 = { var_name : term_subst(sym1,param1) for var_name,term_subst in terms_subst.items() }
            terms_subst_inst2 = { var_name : term_subst(sym2,param2) for var_name,term_subst in terms_subst.items() }
            param1term = param1 | terms_subst_inst1
            param2term = param1 | terms_subst_inst2
            return formula(sym1,sym2,param1term,param2term)
        return res

    def create_equal(self):
        base_equal = self.base_rank.equal
        return self.create_any(base_equal)
        
    def create_reduced(self):
        base_reduced = self.base_rank.reduced
        return self.create_any(base_reduced)

    def create_conserved(self):
        base_conserved = self.base_rank.conserved
        return self.create_any(base_conserved)
    
    def print_structure(self):
        base_rank = self.base_rank
        param_subst = self.param_subst
        print('Subst(',param_subst,', ',end='')
        base_rank.print_structure()
        print(')',end='')

#helper function for classes with existential quantifiers, that allow hints
def insts_from_hints(hints,param,name,sym1,sym2,param1,param2):
    if hints != []:
        instantiations = [ { var_name : var_hint(sym1,sym2,param1,param2) 
                                for var_name,var_hint in hint.items() } for hint in hints]
        existential_vars = []
    else: 
        quant_vars = create_dictionary_of_variables(param,name)
        instantiations = [quant_vars] 
        existential_vars = list(quant_vars.values())
    return (instantiations,existential_vars)

class ParPointwiseFreeRank(FreeRank):
    def __init__(self,
        base_rank: FreeRank,
        param_quant={},
        param={},
        hint_terms_reduced=[]):
        self.base_rank = base_rank
        self.param = param
        self.param_quant = param_quant
        self.hint_terms_reduced = hint_terms_reduced
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved() 

    def check_pointwise(self,formula):
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        def res(sym1,sym2,param1={},param2={}):
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            return ForAll(vars_forall,formula(sym1,sym2,param1forall,param2forall))
        return res
    
    def create_equal(self):
        return self.check_pointwise(self.base_rank.equal)
    
    def create_conserved(self): 
        return self.check_pointwise(self.base_rank.conserved)
        
    def create_reduced(self):
        base_reduced = self.base_rank.reduced
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hints = self.hint_terms_reduced
        def res(sym1,sym2,param1={},param2={}):
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            forall_part = ForAll(vars_forall,base_conserved(sym1,sym2,param1forall,param2forall))

            insts,existential_vars = insts_from_hints(hints,self.param_quant,'_e',sym1,sym2,param1,param2)

            reduced_instantiations = [ base_reduced(sym1,sym2,param1 | inst,param2 | inst) for inst in insts ]
            reduced = Or(reduced_instantiations)

            if len(existential_vars)>0:
                reduced = Exists(existential_vars,reduced)
            
            return And(reduced,forall_part)
        return res
    
    def print_structure(self):
        base_rank = self.base_rank
        param_quant = self.param_quant
        print('ParPW(',param_quant,', ',end='')
        base_rank.print_structure()
        print(')',end='')


def create_vars_sigma(free_vars,
                      varsA,
                      varsB):
    #vars_sigma is a dictionary that holds, for each variable name
    #an if-then-else expression that holds the appropriate value 
    vars_sigma = {name : If(equality_dicts(free_vars,varsA),varsB[name],If(equality_dicts(free_vars,varsB), varsA[name], free_vars[name]))
                  for name in free_vars.keys()
                 }
    return vars_sigma

#should currently keep this class before making sure the generalization is good
class ParPermute2FreeRank(FreeRank):
    #maybe good to allow using paramA vocabulary in hints_B - but kind of tricky to implement and justify
    def __init__(self,base_rank: FreeRank,param_quant={},param={},
                 hint_terms_e=[],hint_terms_A=[],hint_terms_B=[]
                 ):
        self.base_rank = base_rank
        self.param = param
        self.param_quant = param_quant
        self.hint_terms_e = hint_terms_e
        self.hint_terms_A = hint_terms_A
        self.hint_terms_B = hint_terms_B
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()

    def create_equal_or_conserved(self,formula):
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hint_terms_A = self.hint_terms_A
        hint_terms_B = self.hint_terms_B
        def res(sym1,sym2,param1={},param2={}):

            """
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            forall_formula = formula(sym1,sym2,param1forall,param2forall)

            def formula_before_instantiation(inst_A,inst_B):
                return And(
                    formula(sym1,sym2,param1 | inst_A,param2 | inst_B),
                    formula(sym1,sym2,param1 | inst_B,param2 | inst_A),
                    ForAll(vars_forall,Implies(
                        And(Not(equality_dicts(vars_forall_dict,inst_A)),
                            Not(equality_dicts(vars_forall_dict,inst_B))),
                        forall_formula)))
            """

            def formula_before_instantiation(inst_A,inst_B):
                #implementation with if-then-else, will be more compact but maybe worse performance
                #more similar to the paper, y in paper is vars_forall_dict

                vars_sigma = create_vars_sigma(vars_forall_dict,inst_A,inst_B)        
                return ForAll(vars_forall,formula(sym1,sym2,
                               param1 | vars_forall_dict,
                               param2 | vars_sigma
                               ))
            
            insts_A,ex_vars_A = insts_from_hints(hint_terms_A,self.param_quant,'_A',sym1,sym2,param1,param2)
            insts_B,ex_vars_B = insts_from_hints(hint_terms_B,self.param_quant,'_B',sym1,sym2,param1,param2)
            existential_vars = ex_vars_A+ex_vars_B
            insts = [(inst_A,inst_B) for inst_A in insts_A for inst_B in insts_B]

            instantiated_formula = Or([formula_before_instantiation(inst[0],inst[1]) for inst in insts])
            if len(existential_vars)>0:
                instantiated_formula = Exists(existential_vars,instantiated_formula)

            return instantiated_formula
            
        return res

    def create_equal(self):
        return self.create_equal_or_conserved(self.base_rank.equal)
    
    def create_conserved(self):
        return self.create_equal_or_conserved(self.base_rank.conserved)

    def create_reduced(self):
        base_reduced = self.base_rank.reduced
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hint_terms_A = self.hint_terms_A
        hint_terms_B = self.hint_terms_B
        hint_terms_e = self.hint_terms_e
        def res(sym1,sym2,param1={},param2={}):

            """
            old implementation without if-then-else
            def formula_before_instantiation(inst_A,inst_B,inst_e):
                param1forall = param1 | vars_forall_dict
                param2forall = param2 | vars_forall_dict
                forall_leq = base_conserved(sym1,sym2,param1forall,param2forall) 
                paramA1 = param1 | inst_A
                paramA2 = param2 | inst_A
                paramB1 = param1 | inst_B
                paramB2 = param2 | inst_B
                parame1 = param1 | inst_e
                parame2 = param2 | inst_e 
                A1_leq_B2 = base_conserved(sym1,sym2,paramA1,paramB2) 
                B1_leq_A2 = base_conserved(sym1,sym2,paramB1,paramA2)
                A1_less_B2 = base_reduced(sym1,sym2,paramA1,paramB2) 
                B1_less_A2 = base_reduced(sym1,sym2,paramB1,paramA2)
                e_less_e = base_reduced(sym1,sym2,parame1,parame2)
                forall_diffAB = And(Not(equality_dicts(vars_forall_dict,inst_A)),
                                    Not(equality_dicts(vars_forall_dict,inst_B)))
                e_diffAB = And(Not(equality_dicts(inst_e,inst_A)),
                               Not(equality_dicts(inst_e,inst_B)))
                return And(
                    Or(
                    And(equality_dicts(inst_e,inst_A),A1_less_B2),
                    And(equality_dicts(inst_e,inst_B),B1_less_A2),
                    And(e_diffAB,e_less_e)
                    ),
                    A1_leq_B2,
                    B1_leq_A2,
                    ForAll(vars_forall,Implies(forall_diffAB,forall_leq)))
            """

            def formula_before_instantiation(inst_A,inst_B,inst_e):
                vars_sigma_forall = create_vars_sigma(vars_forall_dict,inst_A,inst_B)    
                vars_sigma_exists = create_vars_sigma(inst_e,inst_A,inst_B)   
            
                reduced_part = base_reduced(sym1,sym2,param1 | inst_e, param2 | vars_sigma_exists)
                conserved_part = ForAll(vars_forall,base_conserved(sym1,sym2, param1 | vars_forall_dict, param2 | vars_sigma_forall))

                return And(reduced_part,conserved_part)
            
            insts_A,ex_vars_A = insts_from_hints(hint_terms_A,self.param_quant,'_A',sym1,sym2,param1,param2)
            insts_B,ex_vars_B = insts_from_hints(hint_terms_B,self.param_quant,'_B',sym1,sym2,param1,param2)
            insts_e,ex_vars_e = insts_from_hints(hint_terms_e,self.param_quant,'_e',sym1,sym2,param1,param2)
            existential_vars = ex_vars_A+ex_vars_B+ex_vars_e
            insts = [(inst_A,inst_B,inst_e) for inst_A in insts_A for inst_B in insts_B for inst_e in insts_e]

            instantiated_formula = Or([formula_before_instantiation(inst[0],inst[1],inst[2]) for inst in insts])
            if len(existential_vars)>0:
                instantiated_formula = Exists(existential_vars,instantiated_formula)

            return instantiated_formula
            
        return res
    
    def print_structure(self):
        base_rank = self.base_rank
        param_quant = self.param_quant
        print('ParPerm2(',param_quant,', ',end='')
        base_rank.print_structure()
        print(')',end='')


#The next few constructors are in testing - not finished
#a more general treamtent of permuted pointwise, allowing permutation of multiple pairs of elements.

def create_vars_sigma_list(free_vars,
                      varsA_list,
                      varsB_list):
    #vars_sigma is a dictionary that holds, for each variable name
    #an if-then-else expression that holds the appropriate value 
    k = len(varsA_list)
    vars_sigma = free_vars
    #iteratively add more if-then-else expressions
    for i in range(k):
        varsA = varsA_list[i]
        varsB = varsB_list[i]
        temp = vars_sigma
        vars_sigma = {name : If(equality_dicts(free_vars,varsA),
                                varsB[name],
                                If(equality_dicts(free_vars,varsB), 
                                   varsA[name], 
                                   temp[name]))
                    for name in free_vars.keys()
                    }
    return vars_sigma

def inequalities_for_perm(list_dictsA,list_dictsB):
    #for every i!=j we require A[i]!=A[j],B[i]!=B[j] and A[i]!=B[j]
    n = len(list_dictsA)
    inequalities = []
    for i in range(n):
        for j in range(i):
            inequalities.append(Not(equality_dicts(list_dictsA[i],list_dictsA[j])))
            inequalities.append(Not(equality_dicts(list_dictsB[i],list_dictsB[j])))
            inequalities.append(Not(equality_dicts(list_dictsA[i],list_dictsB[j])))
    return And(inequalities)

def equal_to_one_of_list(free_vars,list_dicts):
    n = len(list_dicts)
    equalities = []
    for i in range(n):
        equalities.append((equality_dicts(list_dicts[i],free_vars)))
        #we give lists_dicts[i] as the first component because it may contain less keys if the hints don't cover all variables
        #not tested
    return Or(equalities)

def mixed_inequalities(list_dictsA,list_dictsB):
    
    pass

class ParPermFreeRank(FreeRank):
    #implementation very much not finished.
    #The hinting is not optimal

    #implemenets the permutation constructor by allowing permutations of the form
    # a_1,....a_k <-> b_1,...,b_k where k is the input num_permute.
    def __init__(self,base_rank: FreeRank,param_quant={},
                 param={},
                 num_permute = 0,
                 hint_terms_e=[],hint_terms_perm=[]
                 ):
        self.base_rank = base_rank
        self.param = param
        self.param_quant = param_quant
        self.num_permute = num_permute
        self.hint_terms_e = hint_terms_e
        self.hint_terms_perm = hint_terms_perm
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()

    def create_equal_or_conserved(self,formula):
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hint_terms_perm = self.hint_terms_perm
        num_permute = self.num_permute

        def res(sym1,sym2,param1={},param2={}):
            def formula_before_instantiation(varsA_list,varsB_list):
                #implementation with if-then-else, will be more compact but maybe worse performance
                #more similar to the paper, y in paper is vars_forall_dict

                vars_sigma = create_vars_sigma_list(vars_forall_dict,varsA_list,varsB_list)    
                inequalities = inequalities_for_perm(varsA_list,varsB_list)
                    
                return And(
                    inequalities,
                    ForAll(vars_forall,formula(sym1,sym2,
                               param1 | vars_forall_dict,
                               param2 | vars_sigma
                               ))
                )
            
            #this works but just creates huge formulas so maybe we can optimize somehow or think of a different solution
            if hint_terms_perm != []:
                hint_combinations = list(itertools.product(hint_terms_perm,repeat=num_permute))
                instantiated_hint_combinations = []
                for hint_comb in hint_combinations:
                    instantiated_hint_combinations.append([ { var_name : var_hint(sym1,sym2,param1,param2) 
                                    for var_name,var_hint in hint.items() } for hint in hint_comb ])
                #something missing here because the hints are not instantiated!! need to uses insts_from_hints
                pairs_of_hint_combos = [(hint_A,hint_B) for hint_A in instantiated_hint_combinations for hint_B in instantiated_hint_combinations]
                instantiated_formula = Or([formula_before_instantiation(pair[0],pair[1]) for pair in pairs_of_hint_combos])
            else:
                sort_dict = self.param_quant
                list_exists_A = [create_dictionary_of_variables(sort_dict,"_A"+str(i)) for i in range(num_permute)]
                list_exists_B = [create_dictionary_of_variables(sort_dict,"_B"+str(i)) for i in range(num_permute)]
                #collect all created variables 
                exists_vars = []
                for i in range(num_permute):
                    exists_vars.extend(list_exists_A[i].values())
                    exists_vars.extend(list_exists_B[i].values())
                instantiated_formula = Exists(exists_vars,formula_before_instantiation(list_exists_A,list_exists_B))

            return instantiated_formula

        return res

    def create_conserved(self): 
        return self.create_equal_or_conserved(self.base_rank.conserved)

    def create_equal(self): 
        return self.create_equal_or_conserved(self.base_rank.equal)

    def create_reduced(self):
        base_reduced = self.base_rank.reduced
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hint_terms_e = self.hint_terms_e
        hint_terms_perm = self.hint_terms_perm
        num_permute = self.num_permute

        def res(sym1,sym2,param1={},param2={}):
            def formula_before_instantiation(varsA_list,varsB_list,inst_e):
                vars_sigma_forall = create_vars_sigma_list(vars_forall_dict,varsA_list,varsB_list)    
                vars_sigma_exists = create_vars_sigma_list(inst_e,varsA_list,varsB_list)   
            
                reduced_part = base_reduced(sym1,sym2,param1 | inst_e, param2 | vars_sigma_exists)
                conserved_part = ForAll(vars_forall,base_conserved(sym1,sym2, param1 | vars_forall_dict, param2 | vars_sigma_forall))

                return And(reduced_part,conserved_part)
            
            if hint_terms_perm != []:
                hint_combinations = list(itertools.product(hint_terms_perm,repeat=num_permute))
                instantiated_hint_combinations = []
                for hint_comb in hint_combinations:
                    instantiated_hint_combinations.append([ { var_name : var_hint(sym1,sym2,param1,param2) 
                                    for var_name,var_hint in hint.items() } for hint in hint_comb ])
                insts_e,ex_vars_e = insts_from_hints(hint_terms_e,self.param_quant,'_e',sym1,sym2,param1,param2)
                triplets_of_hint_combos = [(hint_A,hint_B,inst_e) for hint_A in instantiated_hint_combinations 
                                                               for hint_B in instantiated_hint_combinations
                                                               for inst_e in insts_e]
                instantiated_formula = Or([formula_before_instantiation(triplet[0],triplet[1],triplet[2]) for triplet in triplets_of_hint_combos])
                if len(ex_vars_e)>0:
                    instantiated_formula = Exists(ex_vars_e,instantiated_formula)
            else:
                sort_dict = self.param_quant
                list_exists_A = [create_dictionary_of_variables(sort_dict,"_A"+str(i)) for i in range(num_permute)]
                list_exists_B = [create_dictionary_of_variables(sort_dict,"_B"+str(i)) for i in range(num_permute)]
                exists_vars = []
                for i in range(num_permute):
                    exists_vars.extend(list_exists_A[i].values())
                    exists_vars.extend(list_exists_B[i].values())                    
                insts_e,ex_vars_e = insts_from_hints(hint_terms_e,self.param_quant,'_e',sym1,sym2,param1,param2)
                triplets_of_hint_combos = [(list_exists_A,list_exists_B,inst_e) for inst_e in insts_e]
                instantiated_formula = Or([formula_before_instantiation(triplet[0],triplet[1],triplet[2]) for triplet in triplets_of_hint_combos])
                exists_vars = exists_vars + ex_vars_e
                instantiated_formula = Exists(exists_vars,instantiated_formula) 

            return instantiated_formula

        return res
        

#this works but it would be helpful to have incomplete lists
#or more grandious, to allow a different number of permutations for different hints - radical, doesn't really fit the framework
class ParPermFreeRank_variant(FreeRank):
    #implementation very much not finished.
    
    #implemenets the permutation constructor by allowing permutations of the form
    # a_1,....a_k <-> b_1,...,b_k where k is the input num_permute.
    def __init__(self,base_rank: FreeRank,param_quant={},
                 param={},
                 num_permute = 0,
                 hint_list=[], # [([ ... ],[ ... ]), ... , ([ ... ],[ ... ])] 
                 hint_list_e=[], # [([ ... ],[ ... ],  ), ... , ([ ... ],[ ... ],  )] 
                 ):
        self.base_rank = base_rank
        self.param = param
        self.param_quant = param_quant
        self.num_permute = num_permute
        self.hint_list = hint_list
        self.hint_list_e = hint_list_e
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()

    def create_equal_or_conserved(self,formula):
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hint_list = self.hint_list
        num_permute = self.num_permute

        def res(sym1,sym2,param1={},param2={}):
            def formula_before_instantiation(varsA_list,varsB_list):
                #implementation with if-then-else, will be more compact but maybe worse performance
                #more similar to the paper, y in paper is vars_forall_dict

                vars_sigma = create_vars_sigma_list(vars_forall_dict,varsA_list,varsB_list)    
                inequalities = inequalities_for_perm(varsA_list,varsB_list)
                    
                return And(
                    inequalities,
                    ForAll(vars_forall,formula(sym1,sym2,
                               param1 | vars_forall_dict,
                               param2 | vars_sigma
                               ))
                )
            
            if hint_list != []:
                #instantiate everything before plugging it in the formula
                pairs_list = []
                for hint in hint_list:
                    A_list = hint[0] #list of dictionaries
                    B_list = hint[1]
                    instantiated_A_terms = [ { var_name : var_hint(sym1,sym2,param1,param2) 
                                    for var_name,var_hint in hint.items() } for hint in A_list ]
                    instantiated_B_terms = [ { var_name : var_hint(sym1,sym2,param1,param2) 
                                    for var_name,var_hint in hint.items() } for hint in B_list ]
                    pair = (instantiated_A_terms,instantiated_B_terms)
                    pairs_list.append(pair)
                        
                instantiated_formula = Or([formula_before_instantiation(pair[0],pair[1]) for pair in pairs_list])

            else:
                sort_dict = self.param_quant
                list_exists_A = [create_dictionary_of_variables(sort_dict,"_A"+str(i)) for i in range(num_permute)]
                list_exists_B = [create_dictionary_of_variables(sort_dict,"_B"+str(i)) for i in range(num_permute)]
                #collect all created variables 
                exists_vars = []
                for i in range(num_permute):
                    exists_vars.extend(list_exists_A[i].values())
                    exists_vars.extend(list_exists_B[i].values())
                instantiated_formula = Exists(exists_vars,formula_before_instantiation(list_exists_A,list_exists_B))

            return instantiated_formula

        return res
    
    def create_conserved(self): 
        return self.create_equal_or_conserved(self.base_rank.conserved)

    def create_equal(self): 
        return self.create_equal_or_conserved(self.base_rank.equal)

    def create_reduced(self):
        base_reduced = self.base_rank.reduced
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hint_list_e = self.hint_list_e
        num_permute = self.num_permute

        def res(sym1,sym2,param1={},param2={}):
            def formula_before_instantiation(varsA_list,varsB_list,inst_e):
                vars_sigma_forall = create_vars_sigma_list(vars_forall_dict,varsA_list,varsB_list)    
                vars_sigma_exists = create_vars_sigma_list(inst_e,varsA_list,varsB_list)   
            
                reduced_part = base_reduced(sym1,sym2,param1 | inst_e, param2 | vars_sigma_exists)
                conserved_part = ForAll(vars_forall,base_conserved(sym1,sym2, param1 | vars_forall_dict, param2 | vars_sigma_forall))

                return And(reduced_part,conserved_part)
            
            if hint_list_e != []:
                #instantiate everything before plugging it in the formula
                triplets_list = []
                for hint in hint_list_e:
                    A_list = hint[0] #list of dictionaries
                    B_list = hint[1]
                    e_hint = hint[2]
                    instantiated_A_terms = [ { var_name : var_hint(sym1,sym2,param1,param2) 
                                    for var_name,var_hint in hint.items() } for hint in A_list ]
                    instantiated_B_terms = [ { var_name : var_hint(sym1,sym2,param1,param2) 
                                    for var_name,var_hint in hint.items() } for hint in B_list ]
                    instantiated_e_term = { var_name : var_hint(sym1,sym2,param1,param2)
                                    for var_name,var_hint in e_hint.items() }
                    triplet = (instantiated_A_terms,instantiated_B_terms,instantiated_e_term)
                    triplets_list.append(triplet)
                        
                instantiated_formula = Or([formula_before_instantiation(triplet[0],triplet[1],triplet[2]) for triplet in triplets_list])

            else:
                sort_dict = self.param_quant
                list_exists_A = [create_dictionary_of_variables(sort_dict,"_A"+str(i)) for i in range(num_permute)]
                list_exists_B = [create_dictionary_of_variables(sort_dict,"_B"+str(i)) for i in range(num_permute)]
                exists_e = create_dictionary_of_variables(sort_dict,'_e')
                #collect all created variables 
                exists_vars = list(exists_e.values())
                for i in range(num_permute):
                    exists_vars.extend(list_exists_A[i].values())
                    exists_vars.extend(list_exists_B[i].values())
                instantiated_formula = Exists(exists_vars,formula_before_instantiation(list_exists_A,list_exists_B,exists_e))

            return instantiated_formula

        return res
        

#Doesnt have reduced currently, and has poor performance seemingly.
class ParPermFreeRank_bounded(FreeRank):
    #implementation very much not finished.
    
    #implemenets the permutation constructor by allowing permutations of the form
    # a_1,....a_k <-> b_1,...,b_k where k is the input num_permute.
    def __init__(self,base_rank: FreeRank,param_quant={},
                 param={},
                 num_permute = 0,
                 hint_terms_e=[],hint_terms_bounded=[] # [([ ... ],[ ... ]), ... , ([ ... ],[ ... ])] 
                 ):
        self.base_rank = base_rank
        self.param = param
        self.param_quant = param_quant
        self.num_permute = num_permute
        self.hint_terms_e = hint_terms_e
        self.hint_terms_bounded = hint_terms_bounded
        self.equal = self.create_equal()
        self.reduced = lambda *args: False ####TEMPORARY
        self.conserved = self.create_conserved()


    def create_equal_or_conserved(self,formula):
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hint_terms_bounded = self.hint_terms_bounded
        num_permute = self.num_permute
        sort_dict = self.param_quant

        def res(sym1,sym2,param1={},param2={}):            
            instantiated_hints = [ { var_name : var_hint(sym1,sym2,param1,param2) 
                                    for var_name,var_hint in hint.items() } for hint in hint_terms_bounded ]
            list_exists_A = [create_dictionary_of_variables(sort_dict,"_A"+str(i)) for i in range(num_permute)]
            list_exists_B = [create_dictionary_of_variables(sort_dict,"_B"+str(i)) for i in range(num_permute)]
            exists_vars = []
            for i in range(num_permute):
                exists_vars.extend(list_exists_A[i].values())
                exists_vars.extend(list_exists_B[i].values())
            if hint_terms_bounded!=[]:
                equalities = []
                for i in range(num_permute):
                    exists_A_equals_one_of_terms = equal_to_one_of_list(list_exists_A[i],instantiated_hints)
                    exists_B_equals_one_of_terms = equal_to_one_of_list(list_exists_B[i],instantiated_hints)
                    equalities.append(exists_A_equals_one_of_terms)
                    equalities.append(exists_B_equals_one_of_terms)
                hint_assertion = And(equalities)
            else:
                hint_assertion = BoolVal(True)

            vars_sigma = create_vars_sigma_list(vars_forall_dict,list_exists_A,list_exists_B)    
            inequalities = inequalities_for_perm(list_exists_A,list_exists_B)
                
            return Exists(exists_vars,And(
                hint_assertion,
                inequalities,
                ForAll(vars_forall,formula(sym1,sym2,
                            param1 | vars_forall_dict,
                            param2 | vars_sigma
                            ))
            ))
        
        return res
    
    def create_conserved(self): 
        return self.create_equal_or_conserved(self.base_rank.conserved)

    def create_equal(self): 
        return self.create_equal_or_conserved(self.base_rank.equal)





#helper function for classes which use an order in the system
def strict_immut_order_axioms(order_formula,sort_dict):
    #l is a formula over sym,param1,param2 where param has the same signature as param1,param2
    #this generates the constraints that l defines a strict, immutable order, as described in section 4.4
    vars_forall_dict1 = create_dictionary_of_variables(sort_dict,'_f1')
    vars_forall1 = list(vars_forall_dict1.values())
    vars_forall_dict2 = create_dictionary_of_variables(sort_dict,'_f2')
    vars_forall2 = list(vars_forall_dict2.values())
    vars_forall_dict3 = create_dictionary_of_variables(sort_dict,'_f3')
    vars_forall3 = list(vars_forall_dict3.values())    
    strong_antisym = lambda sym1,sym2: ForAll(vars_forall1+vars_forall2,Implies(
        order_formula(sym1,vars_forall_dict1,vars_forall_dict2),
        Not(order_formula(sym1,vars_forall_dict2,vars_forall_dict1))))
    transitivity = lambda sym1,sym2 : ForAll(vars_forall1+vars_forall2+vars_forall3,Implies(
        And(order_formula(sym1,vars_forall_dict1,vars_forall_dict2),
            order_formula(sym1,vars_forall_dict2,vars_forall_dict3)),
        order_formula(sym1,vars_forall_dict1,vars_forall_dict3)))
    immutability = lambda sym1,sym2: ForAll(vars_forall1+vars_forall2,
        order_formula(sym1,vars_forall_dict1,vars_forall_dict2)==
        order_formula(sym2,vars_forall_dict1,vars_forall_dict2))
    return lambda sym1,sym2 : And(strong_antisym(sym1,sym2),transitivity(sym1,sym2),immutability(sym1,sym2))

class PositionInOrderFreeRank(FreeRank):
    #now the implementation is like in the paper (29/9)
    def __init__(self,
        order_formula=lambda sym,param1,param2: z3.BoolVal(False),
        param_order={},
        terms_subst={},
        param={}
        ):
        self.param = param
        self.param_order = param_order
        self.order_formula = order_formula
        self.terms_subst = terms_subst 
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved() 

    def create_any(self,formula):
        terms_subst = self.terms_subst
        def res(sym1,sym2,param1={},param2={}):
            terms_subst_inst1 = { var_name : term_subst(sym1,param1) for var_name,term_subst in terms_subst.items() }
            terms_subst_inst2 = { var_name : term_subst(sym2,param2) for var_name,term_subst in terms_subst.items() }
            return formula(sym1,sym2,terms_subst_inst1,terms_subst_inst2)
        return res
    
    def create_equal(self):
        order_formula = self.order_formula
        param_order = self.param_order
        def equal_formula(sym1,sym2,param1={},param2={}):
            return And(
                equality_dicts(param1,param2),
                strict_immut_order_axioms(order_formula,param_order)(sym1,sym2)
            )
        return self.create_any(equal_formula)
    
    def create_reduced(self):
        order_formula = self.order_formula
        param_order = self.param_order
        def reduced_formula(sym1,sym2,param1={},param2={}):
            return And(
                order_formula(sym1,param2,param1), #notice par2 < par1
                strict_immut_order_axioms(order_formula,param_order)(sym1,sym2)
            )
        return self.create_any(reduced_formula)
        
    def create_conserved(self):
        order_formula = self.order_formula
        param_order = self.param_order
        def conserved_formula(sym1,sym2,param1={},param2={}):
            return And(
                Or(order_formula(sym1,param2,param1),equality_dicts(param1,param2)),
                strict_immut_order_axioms(order_formula,param_order)(sym1,sym2)
            )
        return self.create_any(conserved_formula)

    def print_structure(self):
        print('Ord',end='')

class ParLexFreeRank(FreeRank):
    def __init__(self,
        base_rank: FreeRank,
        param_quant={},
        order_formula=lambda sym1,param1,param2: z3.BoolVal(False),
        param={},
        hint_terms_reduced=[]):
        self.base_rank = base_rank
        self.param = param
        self.order_formula = order_formula
        self.param_quant = param_quant
        self.hint_terms_reduced = hint_terms_reduced
        self.equal = self.create_equal()
        self.reduced = self.create_reduced_variant()
        self.conserved = self.create_conserved() 

    def check_pointwise(self,formula):
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        def res(sym1,sym2,param1={},param2={}):
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            return ForAll(vars_forall,formula(sym1,sym2,param1forall,param2forall))
        return res
    
    def create_equal(self):
        base_equal = self.base_rank.equal
        equal_pointwise = self.check_pointwise(base_equal)
        param_quant = self.param_quant
        order_formula = self.order_formula
        immut_order = lambda sym1,sym2 : strict_immut_order_axioms(order_formula,param_quant)(sym1,sym2)
        return lambda sym1,sym2,param1,param2: And(
            immut_order(sym1,sym2),
            equal_pointwise(sym1,sym2,param1,param2)   
        )
        
    def create_reduced(self):
        param_quant = self.param_quant
        order_formula = self.order_formula
        immut_order = lambda sym1,sym2 : strict_immut_order_axioms(order_formula,param_quant)(sym1,sym2)

        base_reduced = self.base_rank.reduced
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        hints = self.hint_terms_reduced
        def res(sym1,sym2,param1={},param2={}):
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict

            def formula_before_instantiation(inst_e):
                return And(
                    base_reduced(sym1,sym2,param1 | inst_e,param2 | inst_e),
                    ForAll(vars_forall,Or(
                        base_conserved(sym1,sym2,param1forall,param2forall),
                        order_formula(sym1,inst_e,vars_forall_dict)
                    ))
                )
                        
            insts_e,ex_vars_e = insts_from_hints(hints,self.param_quant,'_e',sym1,sym2,param1,param2)
            instantiated_formula = Or([formula_before_instantiation(inst) for inst in insts_e])
            if len(ex_vars_e)>0:
                instantiated_formula = Exists(ex_vars_e,instantiated_formula)

            with_immut_order = And(instantiated_formula,immut_order(sym1,sym2))
        
            return with_immut_order
            
        return res
        
    def create_reduced_variant(self):
        #currently cant do hints with this variant (which is non-approximant)
        param_quant = self.param_quant
        order_formula = self.order_formula
        immut_order = lambda sym1,sym2 : strict_immut_order_axioms(order_formula,param_quant)(sym1,sym2)

        base_reduced = self.base_rank.reduced
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_exists_dict = create_dictionary_of_variables(self.param_quant,'_e')
        vars_forall = list(vars_forall_dict.values())
        vars_exists = list(vars_exists_dict.values())

        def res(sym1,sym2,param1={},param2={}):
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            param1exists = param1 | vars_exists_dict
            param2exists = param2 | vars_exists_dict

            return And(
                Exists(vars_exists,base_reduced(sym1,sym2,param1exists,param2exists)), #reduced somewhere
                ForAll(vars_forall,Or(
                    base_conserved(sym1,sym2,param1forall,param2forall),
                    Exists(vars_exists,And(
                        base_reduced(sym1,sym2,param1exists,param2exists),
                        order_formula(sym1,vars_exists_dict,vars_forall_dict)
                    ))
                )),
                immut_order(sym1,sym2), 
            )

        return res
    
    def create_conserved(self): 
        reduced = self.reduced 
        base_conserved = self.base_rank.conserved
        conserved_pointwise = self.check_pointwise(base_conserved)
        param_quant = self.param_quant
        order_formula = self.order_formula
        immut_order = lambda sym1,sym2 : strict_immut_order_axioms(order_formula,param_quant)(sym1,sym2)
        return lambda sym1,sym2,param1={},param2={}: And(
            immut_order(sym1,sym2),Or(
            reduced(sym1,sym2,param1,param2),
            conserved_pointwise(sym1,sym2,param1,param2)
        ))
    
    def print_structure(self):
        base_rank = self.base_rank
        param_quant = self.param_quant
        print('ParLex(',param_quant,', ',end='')
        base_rank.print_structure()
        print(')',end='')

class ParLinFreeRank(FreeRank):
    def __init__(self,
        base_rank: FreeRank,
        param_quant,
        cond_formula=lambda sym,param_quant,param_free: z3.BoolVal(True), #formula on sym,param_quant,param_free
        order_formula=lambda sym,param1,param2: z3.BoolVal(False),
        param={},
        hint_terms_first=[],
        hint_terms_second=[]
        ): 
        self.base_rank = base_rank
        self.param = param
        self.order_formula = order_formula
        self.cond_formula = cond_formula
        self.disj_cond = self.create_disjoint_cond()
        self.param_quant = param_quant
        self.hint_terms_first = hint_terms_first
        self.hint_terms_second = hint_terms_second
        #self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved() 

    def create_disjoint_cond(self): #beta in paper
        #something weird with the variables
        cond_formula = self.cond_formula
        order_formula = self.order_formula
        def disj_cond(sym,param_quant,param_free):
            vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
            vars_forall = list(vars_forall_dict.values())
            return And(
                cond_formula(sym,param_quant,param_free),
                ForAll(vars_forall,Implies(
                    order_formula(sym,vars_forall_dict,param_quant),
                    Not(cond_formula(sym,vars_forall_dict,param_free))
                ))   
            )
        return disj_cond

    def two_case_structure(self,conserved_or_reduced):
        order_formula = self.order_formula
        param_quant = self.param_quant
        immut_order = lambda sym1,sym2 : strict_immut_order_axioms(order_formula,param_quant)(sym1,sym2)
        hint_terms_first = self.hint_terms_first
        hint_terms_second = self.hint_terms_second


        disj_cond = self.disj_cond
        def case1(sym1,sym2,param1,param2):
            def formula_before_instantiation(inst):
                return And(
                    conserved_or_reduced(sym1,sym2,inst | param1, inst | param2),
                    disj_cond(sym1,inst,param1),
                    disj_cond(sym2,inst,param2)
                )
            insts_e,ex_vars_e = insts_from_hints(hint_terms_first,self.param_quant,'_e',sym1,sym2,param1,param2)
            instantiated_formula = Or([formula_before_instantiation(inst) for inst in insts_e])
            if len(ex_vars_e)>0:
                instantiated_formula = Exists(ex_vars_e,instantiated_formula)
            return instantiated_formula
        
        def case2(sym1,sym2,param1,param2):
            def formula_before_instantiation(inst_pre,inst_post):
                return And(
                    disj_cond(sym1,inst_pre,param1),
                    disj_cond(sym2,inst_post,param2),
                    order_formula(sym1,inst_post,inst_pre)
                )
            insts_pre,ex_vars_pre = insts_from_hints(hint_terms_first,self.param_quant,'_pre',sym1,sym2,param1,param2)
            insts_post,ex_vars_post = insts_from_hints(hint_terms_second,self.param_quant,'_post',sym1,sym2,param1,param2)
            existential_vars = ex_vars_pre+ex_vars_post
            insts = [(inst_pre,inst_post) for inst_pre in insts_pre for inst_post in insts_post]

            instantiated_formula = Or([formula_before_instantiation(inst[0],inst[1]) for inst in insts])
            if len(existential_vars)>0:
                instantiated_formula = Exists(existential_vars,instantiated_formula)
            return instantiated_formula
        
        return lambda sym1,sym2,param1={},param2={}: And(
            immut_order(sym1,sym2),Or(
            case1(sym1,sym2,param1,param2),
            case2(sym1,sym2,param1,param2)
            )
        )

    def create_reduced(self):
        return self.two_case_structure(self.base_rank.reduced)        

    def create_conserved(self):
        return self.two_case_structure(self.base_rank.conserved)        

    def print_structure(self):
        base_rank = self.base_rank
        param_quant = self.param_quant
        print('ParLin(',param_quant,', ',end='')
        base_rank.print_structure()
        print(')',end='')


#this method checks whether a two vocabulary formula defines an order (but it cannot be an approximation, 
# so this doesnt really fit with the rest of what we do)
def formula_defines_order(formula,sorts,constant_sym,relation_sym,function_sym):
    #this is not really something we use but it was an interesting idea
    state0 = State(sorts,constant_sym,relation_sym,function_sym,'0')
    state1 = State(sorts,constant_sym,relation_sym,function_sym,'1')
    state2 = State(sorts,constant_sym,relation_sym,function_sym,'2')

    #antisymmetry:
    constraint1 = formula(state0.get_dict(),state1.get_dict())
    constraint2 = formula(state1.get_dict(),state0.get_dict())
    constraints_antisym = [constraint1,constraint2]
    print('antisymmetry check:')
    res = sat_check(constraints_antisym)
    print(res[0])
    if res[0] == z3.sat:
        print(res[1].get_universe(sorts[0]))
        print(res[1])

    #transitivity:
    constraint3 = formula(state0.get_dict(),state1.get_dict())
    constraint4 = formula(state1.get_dict(),state2.get_dict())
    constraint5 = Not(formula(state0.get_dict(),state2.get_dict()))
    constraints_tran = [constraint3,constraint4,constraint5]
    print('transitivity check:')
    res = sat_check(constraints_tran)
    print(res[0])
    if res[0] == z3.sat:
        print(res[1].get_universe(sorts[0]))
        print(res[1])

class LivenessProperty:
    #I want to remove this class
    def __init__(self,p,q,rs: list,sort_dicts:list[dict]):
        self.p = p
        self.q = q
        self.rs = rs
        self.sort_dicts = sort_dicts
    
class LivenessProof:
    def __init__(self,prop: LivenessProperty,rank: FreeRank, rho,phi,psis:list):
        self.prop = prop
        self.rank = rank
        self.rho = rho
        self.phi = phi
        self.psis = psis

    def check_proof(self,ts):
        self.print_structure()
        res1 = self.premise_inv(ts)
        res2 = self.premise_trig(ts)
        res3 = self.premise_phi_stability(ts)
        res4 = self.premise_conserved(ts)
        res5 = self.premise_helpful(ts)
        res6 = self.premise_psi_stability(ts)
        res7 = self.premise_reduced(ts)
        result = all([res1,res2,res3,res4,res5,res6,res7])
        if result: 
            print('ok') 
        else: 
            print('fail')
        return all([res1,res2,res3,res4,res5,res6,res7])

    def print_structure(self):
        print('rank structure: ',end='')
        self.rank.print_structure()
        print('')

    def post_process(self,cex):
        #not implemented
        
        #this method will be called from premise_conserved, and premise_reduced
        #it takes a cex returned by these premises and creates an 'explanation' for it
        #which is the concrete values of the function f that the ranking encodes, as described by the paper.
        
        #split cex into two states

        #generate concrete ranking function f 

        #print value on f on two states as pair

        pass

    def premise_inv(self,ts):
        rho = self.rho
        return ts.check_inductiveness(rho)
        
    def premise_trig(self,ts):
        state = ts.create_state("_")
        states=[state]
        rho = self.rho
        p = self.prop.p
        q = self.prop.q
        phi = self.phi
        constraint1 = rho(state.get_dict())
        constraint2 = p(state.get_dict())
        constraint3 = Not(q(state.get_dict()))
        constraint4 = Not(phi(state.get_dict()))
        constraints = [constraint1,constraint2,constraint3,constraint4]
        sat_result = ts.ts_sat_check(constraints,states)
        print("rho & p & ~q -> phi result:",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],state.get_sym())     
        return (sat_result[0] == z3.unsat)
    
    def premise_phi_stability(self,ts):
        state_pre = ts.create_state("_pre")
        state_post = ts.create_state("_post")
        states=[state_pre,state_post]
        phi = self.phi
        q = self.prop.q
        tau = ts.tr 
        constraint1=phi(state_pre.get_dict())
        constraint2=tau(state_pre.get_dict(),state_post.get_dict()) 
        constraint3=Not(q(state_post.get_dict()))
        constraint4=Not(phi(state_post.get_dict()))
        constraints=[constraint1,constraint2,constraint3,constraint4]
        sat_result = ts.ts_sat_check(constraints,states)
        print("phi & tau & ~q' -> phi' result:",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],state_pre.get_sym()+state_post.get_sym())     
        return (sat_result[0] == z3.unsat)
    
    def premise_helpful(self,ts):
        state = ts.create_state("_")
        states=[state]
        phi = self.phi
        psis = self.psis
        sort_dicts = self.prop.sort_dicts
        quant_psis = []
        for i in range(len(psis)):
            psi = psis[i]
            sort_dict = sort_dicts[i]
            if sort_dict != {}:
                var_dict = create_dictionary_of_variables(sort_dict)
                new_variables = list(var_dict.values())
                def quant_psi(sym,i=i,psi=psi,new_variables=new_variables,var_dict=var_dict):
                    return Exists(new_variables,psi(sym,var_dict))
            else:
                def quant_psi(sym,i=i,psi=psi):
                    return psi(sym,{})
            quant_psis.append(quant_psi)
        constraint1 = phi(state.get_dict())
        constraint2 = And([Not(quant_psi(state.get_dict())) for quant_psi in quant_psis])
        constraints = [constraint1,constraint2]  
        sat_result = ts.ts_sat_check(constraints,states)
        print("phi -> exists x. psi_1(x) | ... | psi_n(x) result:",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],state.get_sym())     
        return (sat_result[0] == z3.unsat)
    
    def premise_conserved(self,ts):
        state_pre = ts.create_state("_pre")
        state_post = ts.create_state("_post")
        states=[state_pre,state_post]
        phi = self.phi
        q = self.prop.q
        tau = ts.tr 
        conserved = self.rank.conserved
        constraint1=phi(state_pre.get_dict())
        constraint2=tau(state_pre.get_dict(),state_post.get_dict()) 
        constraint3=Not(q(state_post.get_dict()))
        constraint4=Not(conserved(state_pre.get_dict(),state_post.get_dict()))
        constraints=[constraint1,constraint2,constraint3,constraint4]
        sat_result = ts.ts_sat_check(constraints,states)
        print("phi & tau & ~q' -> rank'<=rank result:",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],state_pre.get_sym()+state_post.get_sym())     
        return (sat_result[0] == z3.unsat)

    def premise_psi_stability(self,ts):
        #NEW VERSION WE ARE USING - ASSUMING ~r and not ~r'
        state_pre = ts.create_state("_pre")
        state_post = ts.create_state("_post")
        states=[state_pre,state_post]
        psis = self.psis
        sort_dicts = self.prop.sort_dicts
        rs = self.prop.rs
        phi = self.phi
        q = self.prop.q
        tau = ts.tr
        n = len(psis)
        results = []
        for i in range(n):
            sorts_i = sort_dicts[i]
            vars = create_dictionary_of_variables(sorts_i)
            psi_i = psis[i]
            r_i = rs[i]
            constraint1=phi(state_pre.get_dict())
            constraint2=tau(state_pre.get_dict(),state_post.get_dict()) 
            constraint3=Not(q(state_post.get_dict()))
            constraint4=psi_i(state_pre.get_dict(),vars)
            constraint5=Not(r_i(state_pre.get_dict(),vars))
            constraint6=Not(psi_i(state_post.get_dict(),vars))
            constraints=[constraint1,constraint2,constraint3,constraint4,constraint5,constraint6]
            sat_result = ts.ts_sat_check(constraints,states)
            print("phi & tau & ~q' & psi_i(x) & ~r_i(x) -> psi_i'(x) result for i =",i,": ",sat_result[0])
            if sat_result[0] == z3.sat and sat_result[1]!=None:
                print_model_in_order(sat_result[1],state_pre.get_sym()+state_post.get_sym())                
            results = results + [sat_result[0]==z3.unsat]
        return all(results)
    
    def premise_reduced(self,ts):
        #VERSION WE ARE USING - ASSUMING r and not r'
        state_pre = ts.create_state("_pre")
        state_post = ts.create_state("_post")
        states=[state_pre,state_post]
        psis = self.psis
        sort_dicts = self.prop.sort_dicts
        rs = self.prop.rs
        phi = self.phi
        q = self.prop.q
        tau = ts.tr
        reduced = self.rank.reduced
        n = len(psis)
        results = []
        for i in range(n):
            sorts_i = sort_dicts[i]
            vars = create_dictionary_of_variables(sorts_i)
            psi_i = psis[i]
            r_i = rs[i]
            constraint1=phi(state_pre.get_dict())
            constraint2=tau(state_pre.get_dict(),state_post.get_dict()) 
            constraint3=Not(q(state_post.get_dict()))
            constraint4=psi_i(state_pre.get_dict(),vars)
            constraint5=r_i(state_pre.get_dict(),vars)
            constraint6=Not(reduced(state_pre.get_dict(),state_post.get_dict()))
            constraints=[constraint1,constraint2,constraint3,constraint4,constraint5,constraint6]
            sat_result = ts.ts_sat_check(constraints,states)
            print("phi & tau & ~q' & psi_i(x) & r_i(x) -> rank' < rank result for i =",i,": ",sat_result[0]) #this is where I changed and rechanged
            if sat_result[0] == z3.sat and sat_result[1]!=None:
                print_model_in_order(sat_result[1],state_pre.get_sym()+state_post.get_sym())                
            results = results + [sat_result[0]==z3.unsat]
        return all(results)

"""

graveyard of old code



class RankingFunction:
    def __init__(self,equal,reduced):
        self.equal = equal 
        self.reduced = reduced
        self.conserved = self.create_conserved()
            
    def create_conserved(self):
        def res(*args):
            return Or(self.equal(*args),self.reduced(*args))
        return res
    
    def print_reduced(self,ts):
        state0 = ts.create_state('0')
        state1 = ts.create_state('1')
        print(self.reduced(state0.get_dict(),state1.get_dict()))

class RankingFunctionConserved(RankingFunction):
    def __init__(self,conserved,reduced):
        self.equal = lambda sym: False
        self.reduced = reduced
        self.conserved = conserved

class BinaryRankingFunction(RankingFunction):
    def __init__(self,predicate):
        #predicate is a function predicate(sym)
        self.predicate = predicate
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = super().create_conserved()

    def create_equal(self):
        pred = self.predicate
        return lambda *args: pred(args[0],*args[2:])==pred(args[1],*args[2:])
    
    def create_reduced(self):
        pred = self.predicate
        return lambda *args: And(pred(args[0],*args[2:]),Not(pred(args[1],*args[2:])))

class IntegerRankingFunction(RankingFunction):
    #When used we need outside guarantee that the var is bounded from below - not implemented currently
    def __init__(self,var_name):
        self.var_name = var_name
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = super().create_conserved()
    
    def create_equal(self):
        var_name = self.var_name
        def res(*args):
            return args[0][var_name]==args[1][var_name]
        return res 
    
    def create_reduced(self):
        var_name = self.var_name
        def res(*args):
            return args[0][var_name] > args[1][var_name]
        return res 

class LexicographicRankingFunction(RankingFunction):
    #initated with [rank_0,...,rank_n] where rank_0 is the strong component
    def __init__(self,ranks : list[RankingFunction]):
        self.ranks = ranks
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = super().create_conserved()

    def create_equal(self):
        comps = self.ranks
        equal = lambda *args : And([comp.equal(*args) for comp in comps])
        return equal
    
    def create_reduced(self):
        #This is how chatgpt suggests to write these methods, with functions instead of lambda functions
        comps = self.ranks
        def res(*args): 
            return False
        for i in range(len(comps)):
            old_part = res
            def new_part(*args,i=i,old_part=old_part):
                return And([comps[i].reduced(*args)] + [comp.equal(*args) for comp in comps[:i]])
            def res(*args,i=i,new_part=new_part,old_part=old_part):
                return Or(new_part(*args), old_part(*args))
        return res
    
    def print_structure(self):
        ranks = self.ranks
        print('Lex(',end='')
        for rank in ranks:
            rank.print_structure()
            print(',',end='')
        print(')',end='')

class OrderLexicographicRank(RankingFunction):

    def __init__(self,free_rank: RankingFunction,sort,order = lambda sym,x,y: False):
        #free_rank is a ranking function for which equal,reduced have 3 arguments (at least) where the 3rd is treated as a var of the given sort
        #order is a function order(sym,x,y) that should be verified to be a (partial,strict) order
        self.rank = free_rank
        self.sort = sort
        self.order = order
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = super().create_conserved()
        
    def create_equal(self):
        rank_equal = self.rank.equal
        variable_name = f"var_{uuid.uuid4()}"
        var0 = create_variable(self.sort,str(self.sort)+str(variable_name))
        return lambda *args: ForAll(var0,rank_equal(args[0],args[1],var0,*args[2:]))

    def create_reduced(self):
        rank_reduced = self.rank.reduced
        rank_conserved = self.rank.conserved
        variable_name1 = f"var_{uuid.uuid4()}"
        variable_name2 = f"var_{uuid.uuid4()}"
        var1 = create_variable(self.sort,str(self.sort)+str(variable_name1))
        var2 = create_variable(self.sort,str(self.sort)+str(variable_name2))
        reduced = lambda *args: Exists(var1,And(
            rank_reduced(args[0],args[1],var1,*args[2:]),
            ForAll(var2,Implies(Not(rank_conserved(args[0],args[1],var2,*args[2:])),
                                    self.order(args[0],var1,var2)))))
        return reduced

class TupleOrderLexicographicRank(RankingFunction):

    def __init__(self,free_rank: RankingFunction,sorts,order = lambda sym,x,y: False):
        #free_rank is a ranking function for which equal,reduced have 3 arguments (at least) where the 3rd is treated as a var of the given tuple sort
        #order is a function order(sym,x,y) that should be verified to be a (partial,strict) order where x,y are tuples
        self.rank = free_rank
        self.sorts = sorts
        self.order = order
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = super().create_conserved()
        
    def create_equal(self):
        rank_equal = self.rank.equal
        sorts = self.sorts 
        n = len(sorts)
        variables = [ create_variable(sorts[i],str(sorts[i])+ f"var_{uuid.uuid4()}"+str(i)) for i in range(n) ]
        return lambda *args: ForAll(variables,rank_equal(args[0],args[1],variables,*args[2:]))

    def create_reduced(self):
        rank_reduced = self.rank.reduced
        rank_conserved = self.rank.conserved
        sorts = self.sorts 
        n = len(sorts)
        variables_forall = [ create_variable(sorts[i],str(sorts[i])+ f"var_{uuid.uuid4()}"+str(i)+"forall") for i in range(n) ]
        variables_exists = [ create_variable(sorts[i],str(sorts[i])+ f"var_{uuid.uuid4()}"+str(i)+"exists") for i in range(n) ]
        reduced = lambda *args: Exists(variables_exists,And(
            rank_reduced(args[0],args[1],variables_exists,*args[2:]),
            ForAll(variables_forall,Implies(Not(rank_conserved(args[0],args[1],variables_forall,*args[2:])),
                                    self.order(args[0],variables_exists,variables_forall)))))
        return reduced

class DirectSumRank(RankingFunction):
    #Perhpas buggy, haven't tested, using the DirectSumFreeRank instead
    def __init__(self,ranks:List[RankingFunction],conditions):
        self.ranks = ranks
        self.conditions = conditions
        self.disjoints_conds = self.create_disjoint_conds()
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = super().create_conserved()
        
    def create_disjoint_conds(self):
        #SOMETHING WRONG
        conditions = self.conditions
        n = len(conditions)
        disj_conds = []
        for i in range(n):
            def disj_cond_i(sym,i=i):
                return And(conditions[i](sym),
                           And([Not(conditions[j](sym)) for j in range(i)]))
            disj_conds.append(disj_cond_i)
        return disj_conds
        #return [lambda sym,conditions=conditions: And(And([Not(conditions[j](sym)) for j in range(i)]),conditions[i](sym)) for i in range(n)]

    def create_equal(self): 
        def equality(sym1,sym2):
            ranks = self.ranks
            disjoint_conds = self.disjoints_conds
            n = len(ranks)
            return Or([And(ranks[i].equal(sym1,sym2),disjoint_conds[i](sym1),disjoint_conds[i](sym2)) for i in range(n)])
        return equality
    
    def create_reduced(self):
        def reduction(sym1,sym2):
            ranks = self.ranks
            disjoint_conds = self.disjoints_conds
            n = len(ranks)
            
            same_comp = Or([And(ranks[i].reduced(sym1,sym2),disjoint_conds[i](sym1),disjoint_conds[i](sym2)) for i in range(n)])

            pairs = [(i, j) for i in range(n) for j in range(i+1, n)]
            diff_comp = Or([And(disjoint_conds[i](sym1),disjoint_conds[j](sym2)) for (i,j) in pairs])

            return Or(same_comp,diff_comp)      
        return reduction
    
class CountRank(RankingFunction):
    def __init__(self,predicate,sort):
        #predicate is a function predicate(sym,x) where x is of the given sort
        self.sort = sort
        self.predicate = predicate
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = super().create_conserved()

    def create_equal(self):
        #cannot be captured exactly, this an over-approximation
        #it is sound but not complete

        pred = self.predicate

        var_name1 =  f"var_{uuid.uuid4()}"
        x = create_variable(self.sort,str(self.sort)+var_name1)
        var_name2 =  f"var_{uuid.uuid4()}"
        y0 = create_variable(self.sort,str(self.sort)+var_name2)
        var_name3 =  f"var_{uuid.uuid4()}"
        y1 = create_variable(self.sort,str(self.sort)+var_name3)

        def approx0(sym1,sym2):
            return ForAll(x,pred(sym2,x)==pred(sym1,x))
        def approx1(sym1,sym2):
            return Exists([y0,y1],And(
                pred(sym1,y0),Not(pred(sym2,y0)),
                Not(pred(sym1,y1)),pred(sym2,y1),
                ForAll(x,Implies(And(x!=y0,x!=y1),pred(sym2,x)==pred(sym1,x)))
            ))
        def equal(sym1,sym2):
            return Or(approx0(sym1,sym2),approx1(sym1,sym2))
        
        return equal
    
    def create_reduced(self):
        #cannot be captured exactly, this an over-approximation
        #it is sound but not complete

        pred = self.predicate

        var_name1 =  f"var_{uuid.uuid4()}"
        x = create_variable(self.sort,str(self.sort)+var_name1)
        var_name2 =  f"var_{uuid.uuid4()}"
        y = create_variable(self.sort,str(self.sort)+var_name2)

        def approx0(sym1,sym2):
            return Exists(y,And(
                pred(sym1,y),Not(pred(sym2,y)),
                ForAll(x,Implies(pred(sym2,x),pred(sym1,x)))
            ))
        def reduced(sym1,sym2):
            return Or(approx0(sym1,sym2))
        
        return reduced

class SumBinaryPred(RankingFunction):
    #Again, all approximations. Can also be made more modular in terms of the approximations
    def __init__(self,predicate,sort1,sort2):
        #predicate is a function predicate(sym,x,y) where x,y are of sorts sort1,sort2
        self.sort1 = sort1
        self.sort2 = sort2
        self.predicate = predicate
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = super().create_conserved()

    def create_equal(self):
        pred = self.predicate

        var_name1 =  f"var_{uuid.uuid4()}"
        x1 = create_variable(self.sort1,str(self.sort1)+var_name1)
        var_name2 =  f"var_{uuid.uuid4()}"
        x2 = create_variable(self.sort1,str(self.sort1)+var_name2)
        var_name3 =  f"var_{uuid.uuid4()}"
        x = create_variable(self.sort1,str(self.sort1)+var_name3)
        var_name4 =  f"var_{uuid.uuid4()}"
        y = create_variable(self.sort2,str(self.sort2)+var_name4)

        def approx0(sym1,sym2):
            #very simple approximation
            return ForAll([x,y],pred(sym2,x,y)==pred(sym1,x,y))

        return approx0
    
    def create_reduced(self):
        pred = self.predicate

        var_name1 =  f"var_{uuid.uuid4()}"
        x1 = create_variable(self.sort1,str(self.sort1)+var_name1)
        var_name2 =  f"var_{uuid.uuid4()}"
        x2 = create_variable(self.sort1,str(self.sort1)+var_name2)
        var_name3 =  f"var_{uuid.uuid4()}"
        x = create_variable(self.sort1,str(self.sort1)+var_name3)
        var_name4 =  f"var_{uuid.uuid4()}"
        y = create_variable(self.sort2,str(self.sort2)+var_name4)

        def approx(sym1,sym2):
            return Exists([x1,x2],And(
                # sum_y P'(x2,y) < P(x1,y) (approx)
                Exists(y,And(pred(sym1,x1,y),Not(pred(sym2,x2,y)))),
                ForAll(y,Implies(pred(sym2,x2,y),pred(sym1,x1,y))),
                # sum_y P'(x1,y) <= P(x2,y) (approx)
                ForAll(y,Implies(pred(sym2,x1,y),pred(sym1,x2,y))),
                # Forall x. x!=x1 & x!=x2 -> sum_y P(x,y) <= P(x,y) (approx)
                ForAll(x,Implies(
                    And(x!=x1,x!=x2),
                    ForAll(y,Implies(pred(sym2,x,y),pred(sym1,x,y)))))
                ))
            
        return approx
"""


"""
class ParLivenessProperty: 
    #each fairness constraint is of the form r(x1,...,xn) which are sorted variables
    def __init__(self,p,q,rs,sort_dicts):
        self.p = p
        self.q = q
        self.rs = rs 
        self.sort_dicts = sort_dicts

class ParLivenessProof(LivenessProof):
    #should be initiated with a ParLivenessProperty

    def premise_helpful(self,ts):
        state = ts.create_state("_")
        states=[state]
        phi = self.phi
        psis = self.psis
        sort_dicts = self.prop.sort_dicts
        quant_psis = []
        for i in range(len(psis)):
            psi = psis[i]
            sort_dict = sort_dicts[i]
            var_dict = create_dictionary_of_variables(sort_dict)
            new_variables = list(var_dict.values())
            def quant_psi(sym,i=i,psi=psi,new_variables=new_variables,var_dict=var_dict):
                return Exists(new_variables,psi(sym,var_dict))
            quant_psis.append(quant_psi)
        constraint1 = phi(state.get_dict())
        constraint2 = And([Not(quant_psi(state.get_dict())) for quant_psi in quant_psis])
        constraints = [constraint1,constraint2]
        sat_result = ts.ts_sat_check(constraints,states)
        print("phi -> exists x. psi_1(x) | ... | psi_n(x) result:",sat_result[0])
        if sat_result[0] == z3.sat and sat_result[1]!=None:
            print_model_in_order(sat_result[1],state.get_sym())     
        return (sat_result[0] == z3.unsat)
    
    def premise_psi_stability(self,ts):
        #NEW VERSION WE ARE USING - ASSUMING ~r and not ~r'
        state_pre = ts.create_state("_pre")
        state_post = ts.create_state("_post")
        states=[state_pre,state_post]
        psis = self.psis
        sort_dicts = self.prop.sort_dicts
        rs = self.prop.rs
        phi = self.phi
        q = self.prop.q
        tau = ts.tr
        n = len(psis)
        results = []
        for i in range(n):
            sorts_i = sort_dicts[i]
            vars = create_dictionary_of_variables(sorts_i)
            psi_i = psis[i]
            r_i = rs[i]
            constraint1=phi(state_pre.get_dict())
            constraint2=tau(state_pre.get_dict(),state_post.get_dict()) 
            constraint3=Not(q(state_post.get_dict()))
            constraint4=psi_i(state_pre.get_dict(),vars)
            constraint5=Not(r_i(state_pre.get_dict(),vars))
            constraint6=Not(psi_i(state_post.get_dict(),vars))
            constraints=[constraint1,constraint2,constraint3,constraint4,constraint5,constraint6]
            sat_result = ts.ts_sat_check(constraints,states)
            print("phi & tau & ~q' & psi_i(x) & ~r_i(x) -> psi_i'(x) result for i =",i,": ",sat_result[0])
            if sat_result[0] == z3.sat and sat_result[1]!=None:
                print_model_in_order(sat_result[1],state_pre.get_sym()+state_post.get_sym())                
            results = results + [sat_result[0]==z3.unsat]
        return all(results)
    
    def premise_reduced(self,ts):
        #VERSION WE ARE USING - ASSUMING r and not r'
        state_pre = ts.create_state("_pre")
        state_post = ts.create_state("_post")
        states=[state_pre,state_post]
        psis = self.psis
        sort_dicts = self.prop.sort_dicts
        rs = self.prop.rs
        phi = self.phi
        q = self.prop.q
        tau = ts.tr
        reduced = self.rank.reduced
        n = len(psis)
        results = []
        for i in range(n):
            sorts_i = sort_dicts[i]
            vars = create_dictionary_of_variables(sorts_i)
            psi_i = psis[i]
            r_i = rs[i]
            constraint1=phi(state_pre.get_dict())
            constraint2=tau(state_pre.get_dict(),state_post.get_dict()) 
            constraint3=Not(q(state_post.get_dict()))
            constraint4=psi_i(state_pre.get_dict(),vars)
            constraint5=r_i(state_pre.get_dict(),vars)
            constraint6=Not(reduced(state_pre.get_dict(),state_post.get_dict()))
            constraints=[constraint1,constraint2,constraint3,constraint4,constraint5,constraint6]
            sat_result = ts.ts_sat_check(constraints,states)
            print("phi & tau & ~q' & psi_i(x) & r_i(x) -> rank' < rank result for i =",i,": ",sat_result[0]) #this is where I changed and rechanged
            if sat_result[0] == z3.sat and sat_result[1]!=None:
                print_model_in_order(sat_result[1],state_pre.get_sym()+state_post.get_sym())                
            results = results + [sat_result[0]==z3.unsat]
        return all(results)
"""

"""
class ParPointwiseFreeRank(FreeRank):
    def __init__(self,base_rank: FreeRank,param_quant={},param={},
                 hint_reduced = lambda sym1,sym2,param1,param2,parame:True):
        #base_rank is a FreeRank, expected to have base_rank.param not empty
        self.base_rank = base_rank
        self.param = param
        self.param_quant = param_quant
        self.equal = self.create_equal()
        self.hint_reduced = hint_reduced
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved() 

    def create_equal(self):
        base_equal = self.base_rank.equal
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        def res(sym1,sym2,param1={},param2={}):
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            return ForAll(vars_forall,base_equal(sym1,sym2,param1forall,param2forall))
        return res
        
    def create_reduced(self):
        base_reduced = self.base_rank.reduced
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        vars_dict_e = create_dictionary_of_variables(self.param_quant,'_e')
        vars_exists = list(vars_dict_e.values())
        hint_reduced = self.hint_reduced
        def res(sym1,sym2,param1={},param2={}):
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            param1exists = param1 | vars_dict_e
            param2exists = param2 | vars_dict_e
            return And(
                Exists(vars_exists,And(
                    base_reduced(sym1,sym2,param1exists,param2exists),
                    hint_reduced(sym1,sym2,param1,param2,vars_dict_e)
                    )),
                ForAll(vars_forall,base_conserved(sym1,sym2,param1forall,param2forall))
            )
        return res
    
    def create_conserved(self): 
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        def res(sym1,sym2,param1={},param2={}):
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            return ForAll(vars_forall,base_conserved(sym1,sym2,param1forall,param2forall))
        return res
"""  

"""
class ParPermute2FreeRank(FreeRank):
    #This is an approximation of the permutation constructor, allowing to permute 2 elements
    #The pointwise constructor can be seen as allowing no permutations.
    #There is some choices to be made still, deciding which of equal/reduced/conserved as the primitive.
    #This matters because these would give different (sound) results
    #Here we stick to defining equality but this might be too weak - if so, revise

    def __init__(self,base_rank: FreeRank,param_quant={},param={},
                 hint_permute = lambda sym1,sym2,param1,param2,paramA,paramB:True,
                 hint_reduced = lambda sym1,sym2,param1,param2,parame:True):
        #base_rank is a FreeRank, expected to have base_rank.param not empty
        self.base_rank = base_rank
        self.param = param
        self.param_quant = param_quant
        self.hint_permute = hint_permute
        self.hint_reduced = hint_reduced
        self.equal = self.create_equal()
        self.reduced = self.create_reduced()
        self.conserved = self.create_conserved()

    def create_equal(self):
        base_equal = self.base_rank.equal
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        vars_dict_A = create_dictionary_of_variables(self.param_quant,'_A')
        vars_dict_B = create_dictionary_of_variables(self.param_quant,'_B')
        vars_exists = list(vars_dict_A.values())+list(vars_dict_B.values())
        hint_permute = self.hint_permute
        def res(sym1,sym2,param1={},param2={}):
            paramA1 = param1 | vars_dict_A
            paramA2 = param2 | vars_dict_A
            paramB1 = param1 | vars_dict_B
            paramB2 = param2 | vars_dict_B
            A1equalB2 = base_equal(sym1,sym2,paramA1,paramB2) 
            B1equalA2 = base_equal(sym1,sym2,paramB1,paramA2)
            forall_diffAB = And(Not(equality_dicts(vars_forall_dict,vars_dict_A)),
                                Not(equality_dicts(vars_forall_dict,vars_dict_B)))
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            forall_equal = base_equal(sym1,sym2,param1forall,param2forall)
            return Exists(vars_exists,And(
                A1equalB2,B1equalA2,
                hint_permute(sym1,sym2,param1,param2,vars_dict_A,vars_dict_B),
                ForAll(vars_forall,Implies(forall_diffAB,forall_equal))
            ))
        return res
        
    def create_reduced(self):
        base_reduced = self.base_rank.reduced
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        vars_dict_e = create_dictionary_of_variables(self.param_quant,'_e')
        vars_dict_A = create_dictionary_of_variables(self.param_quant,'_A')
        vars_dict_B = create_dictionary_of_variables(self.param_quant,'_B')
        all_vars_exists = list(vars_dict_A.values())+list(vars_dict_B.values())+list(vars_dict_e.values())
        hint_permute = self.hint_permute
        hint_reduced = self.hint_reduced
        def res(sym1,sym2,param1={},param2={}):
            paramA1 = param1 | vars_dict_A
            paramA2 = param2 | vars_dict_A
            paramB1 = param1 | vars_dict_B
            paramB2 = param2 | vars_dict_B
            parame1 = param1 | vars_dict_e
            parame2 = param2 | vars_dict_e
            A1_leq_B2 = base_conserved(sym1,sym2,paramA1,paramB2) 
            B1_leq_A2 = base_conserved(sym1,sym2,paramB1,paramA2)
            A1_less_B2 = base_reduced(sym1,sym2,paramA1,paramB2) 
            B1_less_A2 = base_reduced(sym1,sym2,paramB1,paramA2)
            e_less_e = base_reduced(sym1,sym2,parame1,parame2)
            forall_diffAB = And(Not(equality_dicts(vars_forall_dict,vars_dict_A)),
                                Not(equality_dicts(vars_forall_dict,vars_dict_B)))
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            forall_leq = base_conserved(sym1,sym2,param1forall,param2forall)
            return Exists(all_vars_exists,And(
                hint_permute(sym1,sym2,param1,param2,vars_dict_A,vars_dict_B),
                hint_reduced(sym1,sym2,param1,param2,vars_dict_e),
                Or(
                    And(equality_dicts(vars_dict_e,vars_dict_A),
                        A1_less_B2),
                    And(equality_dicts(vars_dict_e,vars_dict_B),
                        B1_less_A2),
                    e_less_e 
                ),
                A1_leq_B2,B1_leq_A2,
                ForAll(vars_forall,Implies(forall_diffAB,forall_leq))
            ))
        return res
    
    def create_conserved(self):
        base_conserved = self.base_rank.conserved
        vars_forall_dict = create_dictionary_of_variables(self.param_quant,'_f')
        vars_forall = list(vars_forall_dict.values())
        vars_dict_A = create_dictionary_of_variables(self.param_quant,'_A')
        vars_dict_B = create_dictionary_of_variables(self.param_quant,'_B')
        vars_exists = list(vars_dict_A.values())+list(vars_dict_B.values())
        hint_permute = self.hint_permute
        def res(sym1,sym2,param1={},param2={}):
            paramA1 = param1 | vars_dict_A
            paramA2 = param2 | vars_dict_A
            paramB1 = param1 | vars_dict_B
            paramB2 = param2 | vars_dict_B
            A1consB2 = base_conserved(sym1,sym2,paramA1,paramB2) 
            B1consA2 = base_conserved(sym1,sym2,paramB1,paramA2)
            forall_diffAB = And(Not(equality_dicts(vars_forall_dict,vars_dict_A)),
                                Not(equality_dicts(vars_forall_dict,vars_dict_B)))
            param1forall = param1 | vars_forall_dict
            param2forall = param2 | vars_forall_dict
            forall_equal = base_conserved(sym1,sym2,param1forall,param2forall)
            return Exists(vars_exists,And(
                A1consB2,B1consA2,
                hint_permute(sym1,sym2,param1,param2,vars_dict_A,vars_dict_B),
                ForAll(vars_forall,Implies(forall_diffAB,forall_equal))
            ))
        return res
"""

