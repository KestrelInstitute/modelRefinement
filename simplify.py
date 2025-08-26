from z3 import *
from utilities import *

# this global is used to signal that cdSimplify returns a changed result
cdSimplifyChange = Bool('cdSimplifyChange')
cdSimplifyChange = False

# prove ante:Expr => conseq:Expr
def verfImpl(ante, conseq):  
    s = Solver()
    s.add(ante)
    s.add(Not(conseq))
#    print("verifying", ante, "=>", conseq)
    result = s.check()
    if sat == result:
        print(s.model())
    return result

# is ante1 /\ ante2 /\ hyp unsat?
def isUnsat(ante1, ante2, hyp):  # ante1,ante2,hyp: Expression
    #print("isUnsat:", ante1, ante2, hyp)
    chk = Solver()
    chk.add(hyp)
    if is_and(ante1):
        #for h in ante1:
        for h in ante1.children():
            if (hyp.get_id() != h.get_id()):
                #print("ante1 h:", h)
                chk.add(h)
    else:
        chk.add(ante1)
    if is_and(ante2):
        #for h in ante2:
        for h in ante2.children():
            if (hyp.get_id() != h.get_id()):
                #print("ante2 h:", h)
                chk.add(h)
    else:
        chk.add(ante2)
    #print("isUnsat result:", chk.check())
    if unsat == chk.check(): # return (unsat == chk.check())
        return True
    return False

# remove atom f from the pool:Expression
def remove(pool, f):
    newPool = Goal()
    for g in pool:
        if (f.get_id() != g.get_id()):
            newPool.add(g)
    return newPool        

# for each atomic disjunct d, simplify the remaining disjuncts wrt ~d
# Assume: is_or(expr)
# context: List(Expr), expr:Expr
# returns e:Goal s.t. context => (expr == e)
def simplifyDisjunction(context, expr):
    print("disjuncts:", expr2List(expr))
    global cdSimplifyChange
    changed = True
    newExpr = expr
    i=0

    while changed:
        print("simplifyDisjunction iteration", i)
        changed = False
        for d in expr2List(newExpr):  # disjuncts
            newClause = d
            if not is_and(d):  # d is atomic
                print("focus on", d)
                for e in newExpr.children():
                    if (d.get_id() != e.get_id()):
                        cdSimplifyChange = False
                        e1 = cdSimplifyE_aux(context + [Not(d)], e)
                        print(e, "->", e1)
                        print("change?", cdSimplifyChange)
                        changed = changed or cdSimplifyChange
                        newClause = Or(newClause, e1.as_expr())
        newExpr = simplify(newClause)
        print("newExpr", newExpr, changed)
        i = i+1
    return newExpr

# if there is an equation var=val in a conjunction, or in LHS of implication,
# then eliminate it and replace all occurrences of var by val
# TODO: use quantification over the var plus QE to acheive this
def varElimination (expr):
    if is_and(expr):
        #print("conjuncts:", expr.children())
        eqs = True
        for h in expr.children():
            #print(h)
            if is_eq(h) and is_const(h.children()[0]):  # TODO: handle other cases too
                var = h.children()[0]
                val = h.children()[1]
                #print("h:", var, "==", val)
                expr = simplify(substitute(expr, [(var,val)]))
                eqs = And(h, eqs)
        expr = simplify(And(eqs,expr))
        #print("varElim result:", expr)
    return expr
        
# context:List(Expr), expr:Expr
# returns e:Goal s.t. context => (expr == e)
def cdSimplifyE_aux(context, expr):   
    #print("cdse_aux assume:")
    context = expr2List(simplify(And(*context)))
    #printList(context) 
    #printList(expr2List(simplify(And(*context)))) 
    #print("  simplify:", expr) 
    global cdSimplifyChange
    result = Goal()
    if isUnsat([], context, expr):
        #print(expr, "is False")
        #print("cdSimplifyChange", cdSimplifyChange)
        result.add(False)
        if not expr == False: #expr.is_false():
            cdSimplifyChange = True
            #print("cdSimplifyChange", cdSimplifyChange)
        return result
    elif isUnsat([], context, Not(expr)):
        #print("is True")
        #print("cdSimplifyChange", cdSimplifyChange)
        result.add(True)
        if not expr == True: #.is_true():
            cdSimplifyChange = True
            #print("cdSimplifyChange", cdSimplifyChange)
        return result

    tDisjunct = Then('simplify', 'split-clause')
    if is_or(expr):  # disjunction
        #print("cases:", tDisjunct(expr))
        contextD = simplify(And(*context,result.as_expr()))
        cls = False
        # simplify expr wrt context
        for d in tDisjunct(expr):  # disjuncts
            #print("case:", And(*d))  # d:List(Expr)
            d1 = cdSimplifyE_aux(expr2List(contextD), simplify(And(*d)))
            #print("d1:", d1)
            cls = Or(d1.as_expr(), cls)
        # simplify cls disjuncts relative to each other
        result.add(simplify(cls))
        #print("or result:", result)
    elif is_and(expr):
        expr = varElimination(expr)
        #print("conjuncts:", expr.children())
        pool = Goal()   # local context
        for h in expr.children():
            #print(h)
            pool.add(h)
        oldc = True; old_res = True
        for c in expr.children():  # conjuncts
            #print("conjunct:", c)
            pool = remove(pool, c)
            if not old_res == True: pool.add(oldc)  #SN: bug fix
            oldc = c
            #print("pool:", pool)
            c1 = cdSimplifyE_aux(context + goal2List(pool) + [result.as_expr()], c)
            #print("c1:", c1.as_expr())
            old_res = c1.as_expr()
            result.add(old_res)
            #print("current result", result)
        #print("and result:", result)
    else:     # is atomic(?);  Implies is normalized to Or
        #print("adding atom", expr)
        result.add(expr)

    #print("result:", result)
    return result

# expr:Expr -> return:Goal
def cdSimplifyE(expr):   
    # print("cdse:", expr) 
    expr = varElimination(expr)
    # print("cdse varElim:", expr)
    result = cdSimplifyE_aux([], expr)
    #print("cdse result:", result)
    return result
        
# V0: return a Goal that is the conjunction of f in expr not implied by ante
def residue0(ante, expr):   # ante,expr:Expression
    #print("find residue of", expr)
    #print("assuming",ante)
    pool = Solver()
    for h in expr.children():  #        print(h)
        pool.add(h)
    result = Goal()
    for f in expr.children():
        chk = Solver()
        chk.add(Not(f))
        chk.add(ante)
        if chk.check() == sat:
            result.add(f)
        #if unsat == chk.check(): #print("eliminating",f)
    #print("result:", result)
    return result

# return a Goal that is the conjunction of f in expr not implied by ante
def residue(ante, expr):   # ante,expr:Expression
    # print("Assuming", str(ante)+",")
    # print("Find residue of", expr)
    result = cdSimplifyE_aux(expr2List(ante), expr)
    #print("result:", result)
    return result

