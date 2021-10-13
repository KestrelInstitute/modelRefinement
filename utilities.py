from z3 import *

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

def printTransition(act, exprs):  # act:String, expr:List(Expression)
    print("Transition:", act)
    #print(And(*exprs))
    i = 0
    for expr in exprs:
        if (expr == True): continue
        print("  ", i, " ", expr)
        i = i+1

# state:Expr, transitions:List(Distionary(Action))
def printModel(state, stateInv, transitions):
    #print("\n-------------------------\nCurrent Model")
    print("State:", state)
    print("State Invariants")
    printState(stateInv)
    #print(stateInv)
    #print("Transitions")
    for tr in transitions:
        printTransition(tr['name'], expr2List(tr['controlPred']) + expr2List(tr['envPred']) + expr2List(tr['actionPred']))
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
    
def is_action(expr, state1):
    vs = get_vars(expr)
    #print("expr vars:", vs, "state1 vars", state1)
    for var in state1:
        if var in vs:
            return True
    return False

def isStatePred(expr, state):
    #print("isp?", expr)
    vs = get_vars(expr)
    #print("expr vars:", vs)
    for var in vs:
        #print("checking", var, "not in", state)
        if not (var in state):
            #print("isp", False)
            return False
    #print("isp", True)
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
    
    
