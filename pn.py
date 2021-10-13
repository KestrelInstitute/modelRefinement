# path normalization code
# assumes the goal is a path property
# python pn.py

from z3        import *
from utilities import *
from simplify  import *
from IntList   import *
from model_sorting  import * 

t0 = Tactic('simplify')
t1 = Tactic('qe-light')  #('qe_rec')
t2 = Tactic('solve-eqs')
t3 = Tactic('propagate-ineqs')
t4 = Tactic('propagate-values')

rewrites = IntListRewrites

# form the weakest control prespec or preAction
# input: act:Action, goal:Expr, preStateInv:Expr,  postState1:List[Var]
# return Goal formula over State x controlVars
def makeWeakestControllablePreSpec(act, goal):
    ante = simplify(And(act['postNode']['invariant'], act['controlPred'], act['controlPred'],
                        act['actionPred']))  #, domainAxioms))
    wcpa = ForAll(act['postNode']['vars'] + act['envVar'] + act['controlVar'],
                   Implies(ante, goal))
    #print("wcpa:", wcpa)
    return wcpa

# Path Normalization by backward propagation conforms to MR paper
# TODO: analyze model to find actions whose post-state is coincident
#       with the goal's post-state
# actList: a reversed path (list) of Actions 
def pn_bp(actList, pathProp):  # recursive 
    if len(actList) == 1: # TODO: test if pathProp is localizable
        print("refined property:", pathProp)
        return
    
    #act = actList[0]
    act = actList.pop(0)
    print("pn_bp:")
    print("   act:", act)
    #print("   actList:", actList)
    print("   prop:", pathProp)
    ante = simplify(And(act['postNode']['invariant'], act['controlPred'], act['controlPred'],
                        act['actionPred']))
    print("ante=",ante)
    #ante = expr2List(ante)
    #print("ante=",ante)
    rs = getRewrites(ante, act['postNode']['vars'] + act['envVar'] + act['controlVar'])
    print("rs=",rs)
    r = simplify(substitute(pathProp, rs + rewrites))
    print(r)
    r = residue(ante, r)
    print("result:", r)
    r = substitute(r.as_expr(), rs + rewrites)
    print("after subst:",r)
    # recurse down the path
    pn_bp(actList, r)

# old version
def pn_bp0(actList, pathProp):  # recursive 
    if len(actList) == 1: # TODO: test if pathProp is localizable
        print("refined property:", pathProp)
        return
    
    #act = actList[0]
    act = actList.pop(0)
    print("pn_bp:")
    print("   act:", act)
    #print("   actList:", actList)
    print("   prop:", pathProp)
    wcpa = makeWeakestControllablePreSpec(act,pathProp)
    print("wcpa:", wcpa)
    # eliminate quantifiers and then simplify
    qewcpaG = Then(t0, t1, t2, t0, t3)(wcpa)[0]  # returns Goal: list of conjuncts
    print("qe simplified:", qewcpaG)
    qewcpa = substitute(qewcpaG.as_expr(), rewrites)
    print("rewritten:", qewcpa)
    qewcpa = simplify(qewcpa)
    print("simplified:", qewcpa)
    
    pn_bp(actList, qewcpa)
    
# invoke path normalization on the model
pn_bp(transitions, safetyProps[0])

