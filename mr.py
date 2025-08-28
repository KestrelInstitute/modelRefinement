# python mr.py

from z3        import *
from utilities import *
from simplify  import *
#from model_FC0  import * # run with MR_Control_Refine_Guards
from model_FC  import *
#from model_Tok import *
#from model_RW  import *
#from model_EC  import *
# from model_sched import *

#Global flags
MR_Control_Refine_Guards = Bool('MR_Control_Refine_Guards')
MR_Control_Refine_Guards = False # True

# common types
# state,state1:List[Var]
# subst:List[Pair(Expr,Expr)]
# stateInv:Expression,
# Action: Dictionary{name:String, actionPred:Expr,
#                    envVar:Expr, envPred:Expr,
#                    controlVar:Expr, controlPred:Expr}
# initProps:List(stateProperty)
# transitions:List(Action),
# safetyProps:List(ActionProperty)

# MR for 1 state, n transitions, list of control+env vars
# conforms to MR paper
# todo:  initially, simplify each transition wrt the state invariant
def mr(state, state1, subst, stateInv, initProps, transitions, safetyProps):

    t0 = Tactic('qe_rec')

    # initial state refinements
    initialState = True
    for initProp in initProps:
        print("Enforcing initial state property:", initProp)
        f0 = simplify(And(initialState,initProp))   #print(f0)
        initialState = cdSimplifyE(f0).as_expr()
    #printState(initialState)

    # refine a node via safety state properties
    for phi in safetyProps:
        if not is_action(phi, state1):  # for state goals
            print("Enforcing state goal:", phi)
            inv0 = And(stateInv, phi)    #print("inv0",inv0)
            inv1 = simplify(inv0)        #print("inv1",inv1)
            newStateInv = simplify(cdSimplifyE(inv1).as_expr())
            #print("newStateInv:", newStateInv)
            delta = residue(stateInv, newStateInv)  # print("delta:", delta)
            stateInv = newStateInv       #print("current state invariant:", stateInv)
        else: # for transition goals
            print("Enforcing transition goal:", phi)
            for actIndex in range(len(transitions)):
                act = transitions[actIndex]
                print("\non transition:", act['name'])
                inv0 = And(act['actionPred'], phi)                #print("inv0:", inv0)
                inv1 = simplify(inv0)                #print("inv1",inv1)
                newActInv = simplify(cdSimplifyE(inv1).as_expr())       #print("newActInv:", newActInv)
                delta = residue(act['actionPred'], newActInv)   #print("delta:", delta)
                act['actionPred'] = newActInv
                #if(len(delta) > 0):
                    #print("new Act:", newActInv)
                #else:
                    #print("no change")
    #print(stateInv, is_expr(stateInv))
    stateInvDelta1 = substitute(stateInv, subst)
    #print("current state invariant:", stateInv)

    # fixpoint iteration loop
    moreWork = Bool('moreWork')
    moreWork = True
    iterCnt = 0

    # loop invariant: 
    while (moreWork == True and iterCnt <= 6):
        moreWork = False
        print("\n----------------\niteration", iterCnt)
        iterCnt = iterCnt + 1
        print("Current Model")
        printModel(state, stateInv, transitions)

        # refine an arc's guard wrt its post-node invariant
        stateInv1 = substitute(stateInv, subst)
        for actIndex in range(len(transitions)):
            act = transitions[actIndex]
            print("\nRefining guard on transition:", act['name'])
            # form the weakest control predecessor formula
            wcTrans = ForAll(state1, Implies(act['actionPred'], stateInvDelta1))
            if len(act['envVar']) > 0:
                wcTrans= ForAll(act['envVar'], Implies(act['envPred'], wcTrans))
            print("wcTrans:", wcTrans)

            # eliminate quantifiers and then simplify
            qewcTransG = t0(wcTrans)[0]  # returns Goal: list of conjuncts
            #print("t0(wcTrans):", qewcTransG)
            newActGuard = simplify(And(act['controlPred'], qewcTransG.as_expr()))
            print("nag:", newActGuard)
            newActGuard = simplify(residue(stateInv, newActGuard).as_expr())
            print("simplified newActGuard:", newActGuard)
            # Compute difference between newActGuard and current guard:
            newActGuardDelta = residue(And(act['controlPred'], stateInv), newActGuard)
            print("newActGuardDelta:", newActGuardDelta)
            if(len(newActGuardDelta) > 0):  
                transitions[actIndex]['controlPred'] = newActGuard
                #print("changed guard:")
                moreWork = True
            #else:
                #print("no change")

        # refine a node invariant wrt its out-arcs and post-state prop
        #print("\nRefining the state invariant")
        guardDisjunction = False
        simplifyTransitions = False
        for actIndex in range(len(transitions)):
            act = transitions[actIndex]
            #print("current transition:", act['actionPred'])
            localGuard = act['controlPred']
            #print("guard for transition", act['name'], ":", localGuard)
            #print("control vars:", act['controlVar'])
            if len(act['controlVar']) > 0:
                localGuard = Exists(act['controlVar'], localGuard)
            guardDisjunction = Or(guardDisjunction, localGuard)
        print("guardDisjunction:", guardDisjunction)
        projectGuardG = t0(guardDisjunction)[0]
        #print("projectGuardG", projectGuardG)
        guardDisjunction = simplify(projectGuardG.as_expr())
        print("simplified guard disjunction:", guardDisjunction)
        invariantDelta = residue(stateInv, guardDisjunction) # returns Goal list
        #print("invariantDelta:", invariantDelta)
        if(len(invariantDelta) > 0):  # have a refined state invariant
            stateInv = cdSimplifyE(simplify(And(stateInv, *invariantDelta))).as_expr()
            #print("new State invariant:", stateInv)
            stateInvDelta1 = substitute(And(*invariantDelta), subst)
            print("stateInvDelta1:", stateInvDelta1)
            moreWork = True
            # now simplify each transition's guard wrt the new state invariant
            for actIndex in range(len(transitions)):
                act = transitions[actIndex]
                #print("simplifying guard of", act['name'])
                actGuard = act['controlPred']
                #print("actGuard:", actGuard)
                newActGuard = residue(stateInv, actGuard).as_expr()
                #print("newActGuard:", newActGuard)
                act['controlPred'] = newActGuard
        #else:  #print("no change")

    if moreWork == False:
        print("\n----------------\nFinal Model - fixpoint at iteration", iterCnt)
    else:
        print("\n----------------\nFinal Model - after iteration", iterCnt)
    printModel(state, stateInv, transitions)

    
# invoke model refinement on the model
mr(state, state1, subst, stateInv, initProps, transitions, safetyProps)

