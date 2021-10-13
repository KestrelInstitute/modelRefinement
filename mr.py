# python mr.py

from z3        import *
from utilities import *
from simplify  import *

from model_FC  import *
#from model_FCR  import *
#from model_SE import *
#from model_RW  import *
#from model_EC  import *
#from model_sched import *

# common types
# state,state1:List[Var]
# subst:List[Pair(Expr,Expr)]
# stateInv:Expression,
# Node:   Dictionary{name:String, vars:VarList, invariant:Expr}
# Action: Dictionary{name:String, actionPred:Expr,
#                    envVar:Expr, envPred:Expr,
#                    controlVar:Expr, controlPred:Expr}
# initProps:List(stateProperty)
# transitions:List(Action),
# safetyProps:List(ActionProperty)

# form the weakest control predecessor formula over State x controlVars
# input: act:Action, state1:List[Var],  stateInvDelta1:Expression
# return formula over State x controlVars
def makeWeakestControllablePredecessor(act, state1, stateInvDelta1):
    if act['precNode'] == act['postNode']:
        wcp = ForAll(state1, Implies(act['actionPred'], stateInvDelta1))
    else:
        wcp = ForAll(act['postNode']['vars'], Implies(act['actionPred'], stateInvDelta1))
    if len(act['envVar']) > 0:
        wcp= ForAll(act['envVar'], Implies(act['envPred'], wcp))
        #print("wcp:", wcp)
    return wcp

# model refinement solver
# todo:  initially, simplify each transition wrt the state invariant
def mr(state, state1, subst, stateInv, initProps, transitions, safetyProps):

    t0 = Tactic('qe_rec')

    # initial state refinements
    initialState = True
    for initProp in initProps:
        print("Localizing initial state property:", initProp)
        f0 = simplify(And(initialState,initProp))   #print(f0)
        initialState = cdSimplifyE(f0).as_expr()    #printState(initialState)

    # refine a node via state and action properties
    for phi in safetyProps:
        if not is_action(phi, state1):  # for state goals
            print("\nLocalizing state goal:", phi)
            inv1 = simplify(And(stateInv, phi))    
            newStateInv = simplify(cdSimplifyE(inv1).as_expr())
            print("newStateInv:", newStateInv)
            delta = residue(stateInv, newStateInv)  # print("delta:", delta)
            stateInv = newStateInv       #print("current state invariant:", stateInv)
        else: # for action goals
            print("\nLocalizing action goal:", phi)
            for actIndex in range(len(transitions)):
                act = transitions[actIndex]
                print("\non transition:", act['name'])
                inv0 = And(act['actionPred'], phi)
                inv1 = simplify(inv0)             
                newActInv = simplify(cdSimplifyE(inv1).as_expr())
                delta = residue(act['actionPred'], newActInv)
                act['actionPred'] = newActInv
                if(len(delta) > 0):
                    print("new Act:", newActInv)
                else:
                    print("no change")
    stateInvDelta1 = substitute(stateInv, subst)

    # fixpoint iteration loop
    moreWork = Bool('moreWork')
    moreWork = True
    iterCnt = 0

    # loop invariant: 
    while (moreWork == True and iterCnt <= 10):
        moreWork = False
        print("\n----------------\niteration", iterCnt)
        print("Current Model")
        printModel(state, stateInv, transitions)
        iterCnt = iterCnt + 1

        # refine an arc's guard wrt its post-node invariant
        stateInv1 = substitute(stateInv, subst)
        for actIndex in range(len(transitions)):
            act = transitions[actIndex]
            print("\nRefining guard on transition:", act['name'])
            # form the weakest control predecessor formula
            wcp = makeWeakestControllablePredecessor(act, state1, stateInvDelta1)
            print("wcp:", wcp)

            # eliminate quantifiers and then simplify
            qewcpG = t0(wcp)[0]  # returns Goal: list of conjuncts
            #print("t0(wcp):", qewcpG)
            newActGuard = simplify(And(act['controlPred'], qewcpG.as_expr()))
            #print("nag:", newActGuard)
            newActGuard = simplify(residue(stateInv, newActGuard).as_expr())
            #print("simplified newActGuard:", newActGuard)
            # Compute difference between newActGuard and current guard:
            newActGuardDelta = residue(And(act['controlPred'], stateInv), newActGuard)
            #print("newActGuardDelta:", newActGuardDelta)
            if(len(newActGuardDelta) == 0):  
                print("no change")
            else:
                transitions[actIndex]['controlPred'] = newActGuard
                print("changed guard:", newActGuard)
                moreWork = True

        # refine a node invariant wrt its out-arcs and post-state prop
        print("\nRefining the state invariant")
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
        #print("Total guard:", guardDisjunction)
        projectGuardG = t0(guardDisjunction)[0]
        #print("projectGuardG", projectGuardG)
        guardDisjunction = simplify(projectGuardG.as_expr())
        #print("simplified Total guard:", guardDisjunction)
        invariantDelta = residue(stateInv, guardDisjunction) # returns Goal list
        #print("invariantDelta:", invariantDelta)
        if(len(invariantDelta) == 0):
            print("no change")
        else:  # have a refined state invariant
            stateInv = cdSimplifyE(simplify(And(stateInv, *invariantDelta))).as_expr()
            print("new State invariant:", stateInv)
            stateInvDelta1 = substitute(And(*invariantDelta), subst)
            #print("stateInvDelta1:", stateInvDelta1)
            moreWork = True
            # now simplify each transition's guard wrt the new state invariant
            for actIndex in range(len(transitions)):
                act = transitions[actIndex]
                #print("simplifying guard of", act['name'])
                actGuard = act['controlPred']
                #print("actGuard:", actGuard)
                newActGuard = residue(stateInv, actGuard).as_expr()
                print("new guard:", newActGuard)
                act['controlPred'] = newActGuard

    if moreWork == False:
        print("\n----------------\nFinal Model - fixpoint at iteration", iterCnt)
    else:
        print("\n----------------\nFinal Model - after iteration", iterCnt)
    printModel(state, stateInv, transitions)

    
# invoke model refinement on the model
#if len(transitions) == 1:
#    mr_1_1(state, state1, subst, stateInv, initProps, transitions, safetyProps)
#else:
mr(state, state1, subst, stateInv, initProps, transitions, safetyProps)

