'''
TBD:
- dont think DOING_FORALL_EXISTS is correctly used
- migrate the other examples to the new model format

'''
from z3 import *
DBG2 = True

t0 = Tactic('qe_rec')

def isEmpty(xs): return len(xs) == 0

def printState0(i, expr):  # expr:Expression
    if is_and(expr):
        fs = expr.children()
        print("current state",i)
        for i in range(len(fs)):
            print(i, " ", fs[i])
    else:
        print("current state",i)
        print(i, " ", expr)

def printState(expr):  # expr:Expression
    if is_and(expr):
        fs = expr.children()
        for i in range(len(fs)):
            print("  ", i, " ", fs[i])
    else:
        print(expr)

def printList(es):  # es:List(Expression)
    for i in range(len(es)):
        print("  ", es[i])

def printTransition0(actname, exprs):  # act:String, expr:List(Expression)
    print("Transition:", actname)
    #print(And(*exprs))
    i = 0
    for expr in exprs:
        if (expr == True): continue
        print("  ", i, " ", expr)
        i = i+1

def printTransition(act):  # act:Dictionary
    exprs = []
    if hasattr(act, 'envPred'):
        exprs = exprs + expr2List(act.envPred)
        # print("  EnvPred:", act.envPred)
    if hasattr(act, 'controlPred'):
        exprs = expr2List(act.controlPred)
    if hasattr(act, 'actionPred'):
        exprs = exprs + expr2List(act.actionPred)
    printTransition0(act.name, exprs)

'''Unused
# state:Expr, transitions:List(Distionary(Action))
def printModel0(state, stateInv, transitions):
    #print("\n-------------------------\nCurrent Model")
    print("State:", state)
    print("State Invariants")
    printState(stateInv)
    #print(stateInv)
    #print("Transitions")
    for tr in transitions:
        printTransition(tr['name'], expr2List(tr['controlPred']) + expr2List(tr['envPred']) + expr2List(tr['actionPred']))
    print()
'''
def printModel(model): # state, stateInv, transitions):
    #print("\n-------------------------\nCurrent Model")
    if hasattr(model, 'step_invariant'): print("  Step Invariant:", model.step_invariant)
    for node in model.nodes:
        if hasattr(node, "name"): print("Node:", node.name)
        if hasattr(node, "vars"): print("  Vars:", node.vars)
        if hasattr(node, "invariant"): print("  Node Invariant:", node.invariant) # printState(stateInv)
        if hasattr(node, "envPred"): print("  EnvPred:", node.envPred)
    for act in model.transitions:
        # printTransition0(act.name, expr2List(act.controlPred)
        #                 + expr2List(act.envPred)
        #                 + expr2List(act.actionPred))
        printTransition(act)
    print()

# doesn't work - how to form an equality formula?
def model2Expr(m):
    print("model2Expr")
    result = True
    for d in m.decls():
        print(d.name(), "==", m[d])
        result = And(Eq(d,m[d]), result)
        print(result)
    print(simplify(result))
    return simplify(result)

# code from ~Documents/Code/z3-master/build/python/z3/z3util.py
def vset(seq, idfun=None, as_list=True):
    def _uniq_normal(seq):
        d_ = {}
        for s in seq:
            if s not in d_:
                d_[s] = None
                yield s
 
    def _uniq_idfun(seq,idfun):
        d_ = {}
        for s in seq:
            h_ = idfun(s)
            if h_ not in d_:
                d_[h_] = None
                yield s
 
    if idfun is None:
        res = _uniq_normal(seq)
    else: 
        res = _uniq_idfun(seq,idfun)
 
    return list(res) if as_list else res 

def is_expr_val(v):
    return is_const(v) and v.decl().kind()!=Z3_OP_UNINTERPRETED

#   >>> get_vars(Implies(And(x+y==0,x*2==10),Or(a,Implies(a,b==False))))
#  [x, y, a, b]
def get_vars(f, rs = None):
    if rs is None:
        rs = []
    if is_const(f):
        if is_expr_val(f):
            return rs
        else:  #variable
            return vset(rs + [f],str)
    else:
        for f_ in f.children():
            rs = get_vars(f_, rs)
        return vset(rs, str)


# vars, vars1: List(Expr) of same length
def makeSubstitution(vars, vars1):
    subst = nil
    for index in range(len(vars)):
        subst = cons((vars[index], vars1[index]), subst)
    return subst

'''if expr contains even a single action var its an action pred'''    
def isAction(expr, action_vars):
    #ASSUME: not isNodePred(expr)
    expr_vars = get_vars(expr)
    #print("expr vars:", expr_vars, "state1 vars", state1)
    for var in action_vars:
        if var in expr_vars:
            return True
    return False

'''check if expr is pred that involves only the state vars'''
def isStatePred(expr, vars):  #print("isp?", expr)
    expr_vars = get_vars(expr)        #print("expr vars:", expr_vars)
    for var in expr_vars:             #print("checking", var, "not in", state)
        if not (var in vars): #print("isp", False)
            return False
    #print("isp", True)
    return True

"""check if the expr is a predicate on non updateable vars (other than state vars) """
def isNodePred(expr, node, model=None):
    expr_vars = get_vars(expr)  #print("IsOtherNodePred: testing expr vars:", expr_vars)
    for var in expr_vars:
        if  (model is None or not ((hasattr(model, 'constants') and var in model.constants))) and\
            (model is None or not ((hasattr(model, 'externals') and var in model.externals))) and\
            not (var in node.vars): 
            return False
    return True

'''check for either of the above two cases'''
# def isNodePred(expr, node, model=None): #print("inp?", expr)
#     return isStatePred(expr, node.vars) or \
#            (not (model is None) and isOtherKindOfNodePred(expr, node, model))
    # expr_vars = get_vars(expr); #print("IsNodePred: testing expr vars:", expr_vars)
    # for var in expr_vars:      
    #     if not (var in node.vars or 
    #             # (hasattr(node, 'envVars') and var in node.envVars) or 
    #             # (hasattr(node, 'controlVars') and var in node.controlVars)): # or
    #             (hasattr(model, 'constants') and var in model.constants) or 
    #             (hasattr(model, 'externals') and var in model.externals)):
    #         # print("isNodePred", False)
    #         return False  #print("isp", True)
    # return True

def isArcPred(expr, transition, model):
    if isNodePred(expr, transition.precNode, model) or isNodePred(expr, transition.postNode, model):
        return False
    """ SN: added this to handle the case of self arc on a node """
    if transition.precNode == transition.postNode and isAction(expr, transition.precNode.postVars + transition.controlVars): # + transition.postNode.tempVars):
        return True
    expr_vars = get_vars(expr)
    #print("expr vars:", expr_vars, "state1 vars", state1)
    '''this handling the case of an arc between nodes, in which case instead of post state vars there will be state vars of tgt node'''
    precvars = transition.precNode.vars
    postvars = transition.postNode.vars
    for var in expr_vars:
        if not(var in precvars or var in postvars):
            return False
    return True

# convert g:Goal to a List(Expr)
def goal2List(g):
    if is_and(g.as_expr()):
        return g.as_expr().children()
    return [g.as_expr()]

# convert g:Expr to a List(Conjuncts/Expr)
def expr2List(ex):
    if is_and(ex):
        return ex.children()
    if is_or(ex):
        return ex.children()
    return [ex]

# decide forall(x) x in vs => x in vars
def allIn(vs, vars):
    for x in vs:
        if x not in vars:
            return False
    return True

# convert equality to a rewrite
def eq2rewrite(eq, qevars):
    print("eq:", eq)
    print("qevars:", qevars)
    if is_eq(eq):
        cs = eq.children()
        vs0 = get_vars(cs[0])
        if allIn(vs0, qevars):
            return (cs[0], cs[1])
        else:
            vs1 = get_vars(cs[1])
            if allIn(vs1, qevars):
                return (cs[1], cs[0])
    return

def getRewrites(expr, qevars):
    print("gR expr", expr)
    result = []
    for eq in expr2List(expr):  # .children():
        subst = eq2rewrite(eq, qevars)
        print("subst",subst)
        if not subst == None:
            result = result + [subst]
    return result


# def getGuard(act, node, model):
#   return getGuard1(act.actionPred, node, model)

# def getGuard1(action_pred, node, model):
#     #print("gg:", act, state_vars)
#     result = []
#     for pred in expr2List(action_pred):
#         #print("pred:", pred)
#         if hasattr(model, 'DOING_FORALL_EXISTS') and model.DOING_FORALL_EXISTS: 
#             if isNodePred(pred,node, model):
#                 result.append(pred)
#         else:
#             if isStatePred(pred,node.vars):
#                 result.append(pred)
#     #print("result", result)
#     guard = And(*result)
#     guard = simplify(guard, local_ctx=True)
#     # print("guard: ", guard)
#     return guard
'''this below only makes sense if ctrol pred was carefully updated so as to exclude any conjuncts belonging to the action pred, but dont currently do that
def getGuard(act, node, model):
    result = []
    for pred in expr2List(act.actionPred):
        if isNodePred(pred,node, model):
            result.append(pred)
    #print("result", result)
    guard = And(*result, act.controlPred) # was guard = And(*result)
    guard = simplify(guard, local_ctx=True)
    # print("guard: ", guard)
    return guard
def getGuard(act):
    return act.controlPred if hasattr(act, 'controlPred') else True
'''
""" def getCtrlPred(model, act):
    g = getGuard(act)
    if hasattr(model,'DOING_FORALL_EXISTS') and model.DOING_FORALL_EXISTS:
        g = getConjNotContaining(g, act.precNode.postVars)
    else:
        g = getConjNotContaining(g, act.envVars + act.precNode.postVars)
    return g """

""" def getGuard(act):
    # print("foo", getFoo(act.actionPred, act.precNode.postVars))
    return And(act.controlPred, getConjNotContaining(act.actionPred, act.precNode.postVars)) if hasattr(act, 'controlPred') else True """

# def getFoo(actionPred, vars):
#     #*TBD: need to fix this for multiiplayer, ie dont use postvars
#     return getConjNotContaining(actionPred, vars)
# 
""" def strengthenGuard(act,guard):
    # new_act_pred = simplify(And(*cdSimplifyE(And(guard, act.actionPred))), local_ctx=True)
    new_act_pred = simplify(And(guard, act.actionPred), local_ctx=True)
    # new_act_pred = simplify(And(wp_x, act.actionPred))
    # new_act_pred = simplify(And(wp_x, act.actionPred))
    if DBG2: print("new actionPred:\n" + str(new_act_pred))
    act.actionPred = new_act_pred """

""" def replaceGuard(act, guard):
    #pull out the existing guard -> (guard, action part)
    action_part = getConjContaining(act.actionPred, act.precNode.postVars)
    act.actionPred = And(guard, action_part) """

def simplifyAndQE(formula):
    formula_simp = simplify(formula)
    # if DBG2: print('formula_simp = \n', formula_simp)
    # eliminate quantifiers and then simplify
    formula_qe = t0(formula_simp)[0]  # returns Goal: list of conjuncts
    #print("t0(wcTrans):", qewcTransG)
    formula_e = simplify(formula_qe.as_expr())
    return formula_e

def containsVars(expr, vs):
    all_vars = get_vars(expr)
    return not set(all_vars).isdisjoint(vs)

def getConjNotContaining(p, vs):
    result = []
    for c in expr2List(p):
        #print("c:", c)
        if not containsVars(c,vs):
            result.append(c)
    #print("result", result)
    result = And(*result)
    result = simplify(result, local_ctx=True)
    return result

def getConjContaining(p, vs):
    result = []
    for c in expr2List(p):
        #print("c:", c)
        if containsVars(c,vs):
            result.append(c)
    #print("result", result)
    result = And(*result)
    result = simplify(result, local_ctx=True)
    return result

def implies(p,q):
    return not p or q
