# MR v3: 
# - refactored
# - handles multinode models
# - permits both "\A e. E(). \E u. U()" and "\E u. U(). \A e. E()" forms
# - includes explicit refinement of guard condition
# Notes:
# "control pred" is U
# "guard" is the expression that determines whether an arm (action) is enabled, and is what's OR'd into the giant disjunction. It does not contain u or e because its formed by QE on "\A e. E(e). \E u. U(u,e). wcp" expr or its corresponding \E \A form. 
# U is updated twice - 1. its strengthened by U /\ ewcp/wcp, and the 2nd time its done when the invariant gets updated to shrink it down.

# python mr.py

# TBD:
# why is envVars and envPred on the action shouldnt it be on the node. Only example that has different env vars for different actions is EC

# TODO: implement forward inference from InitProps to get an initial invariant per node

from z3        import *
from utilities import *
from simplify  import *
#set_param('parallel.enable', True) # slows MR down!?
# uncomment to prettyprint large expressions
#set_option(max_args=10000, max_lines=10000, max_depth=10000, max_visited=10000)

# Working Examples
# from model_FC import *
from model_plan import *
# from model_Cinderella import *

DBG2 = True; DBG3=False
moreWork = True  # declaring a global, used to signal that something changed in an iteration
# TYPES
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

#tSimp = Tactic('simplify')
t0 = Tactic('qe_rec')

nodes       = model.nodes
transitions = model.transitions
origControlPreds = {}
for act in transitions:
    origControlPreds[act.name] = act.controlPred

def initInvsWithSafetyProps():
    # refine a node via state and action properties
    for phi in safetyProps:
        print("\nInitializing node [arc] label with state [step] property\n", phi)
        for node in nodes:
            # node.invariant = BoolVal(True)  # init the invariant
            if isNodePred(phi, node, model):  # for state goals
                #SN: i think this is conjoining and simplifying phi wrt any pre-existing inv on node
                print(" on node", node.name)
                inv1 = simplify(And(node.invariant, phi), local_ctx=True)
                newStateInv = simplify(cdSimplifyE(inv1).as_expr(), local_ctx=True)
                #print("  derived node invariant:", newStateInv)
                delta = residue(node.invariant, newStateInv)  # print("delta:", delta)
                #print("delta:", delta)
                node.invariant = newStateInv
                # print("  refined state invariant:", node.invariant)
                print("--> strengthened node label:\n", node.invariant)
                node.stateInvDelta = newStateInv
            else: print(phi, "is not a node predicate for", node.name)
        # step_invariant is a step prop that isn't equational and should not therefore be part of the calc. of the wpc, since it shouldnt be a state inv
        for act in transitions: # for action goals
            if isArcPred(phi, act, model):
                print(" on transition:", act.name)
                model.step_invariant = simplify(And(model.step_invariant, phi), local_ctx=True)
                # print("step inv:", inv)
                print("--> strengthened step invariant:\n", model.step_invariant)
            elif not isNodePred(phi, node, model): 
                print("**ERROR: property", phi, "is not a node or arc pred. Continuing with any remaining predicates")
        # else we have a path predicate; TODO: call pn
    # not all step props have pre and post vars (eg see model_plan) 
    if 'stepProps' in globals(): 
      for phi in stepProps:
        print("\nInitializing arc label with step property\n", phi)
        for act in transitions: # for action goals
                print(" on transition:", act.name)
                model.step_invariant = simplify(And(model.step_invariant, phi), local_ctx=True)
                print("--> strengthened step invariant:\n", model.step_invariant)

def mkNewGuard(act, node, stateInvDeltaX):
  wpc = mkWPC(act, stateInvDeltaX)
  print('wpc', wpc)
  if hasattr(model, "DOING_FORALL_EXISTS") and model.DOING_FORALL_EXISTS:
    #this is \A e. E(s,e) --> \E u. U(s,e,u). L(s')
    print("\nupdating control pred..\n")
    ctrlPred = updCtrlPred(act, node, wpc)  #U <- U & wpc
    # ctrlPred = updGuard(act, node, wpc)
    cwpc = wrapWithCtrl(act, ctrlPred)      #cwpc <- \E u. U
    if DBG2: print('cwpc=', str(cwpc)) 
    wpc = wrapWithEnv(act, node, cwpc)
  else:
    #this is \E u. U(s,e,u) /\ \A s'. act(s,s'). L(s')
    ewpc = wrapWithEnv(act, node, wpc)  #this is \E u. U(s,e,u).L(s')
    ctrlPred = updCtrlPred(act, node, ewpc)
    if DBG2: print('ctrlPred=', str(ctrlPred)) 
    wpc = wrapWithCtrl(act, ctrlPred)
  print('wrapped wpc after QE and simplification = \n', str(wpc))

  all_wps_4_cmpt_transs = mkWPToEnsureAnyTgtTransIsValid(act, node)
  #SN: this is doing U_a <- U_a /\ wcp. Why am i not using it?
  # nib1 = simplify(And(*cdSimplifyE(And(guard, wp_e))), local_ctx=True)
  wp_x = simplify(And(*cdSimplifyE(And(wpc,all_wps_4_cmpt_transs))))

  return wp_x,ctrlPred


'''in the paper this is the L(e,u,F(s)) term. But more generally its T(s,s',e,u) --> L(s'), simplified and QEd'''
def mkWPC(act, stateInvDeltaX): 
    postNode = act.postNode
    if hasattr(postNode, "tempVars"): 
        temp_vars = postNode.tempVars
    else:
        temp_vars = []
    if act.precNode == postNode:        #ie. self loop action
        # print ('postNode[invariant]', postNode.invariant)
        # postNodeInv = postNode.invariant
        # # if postNode.invariant != True:
        # if not is_true(postNode.invariant):
        #     postNodeInv = substitute(postNode.invariant, postNode.subst)
        # wp = Implies(act.actionPred, postNodeInv)
        step_wpc = True
        # if hasattr(model, "step_invariant") and not (model.step_invariant == True):
        #   step_wpc = Implies(And(act.precNode.invariant, act.actionPred, act.strengthening), 
        #                      model.step_invariant)
        #   step_wpc = ForAll(postNode.postVars, step_wpc)
        #   step_wpc = simplify(cdSimplifyE(step_wpc).as_expr(), local_ctx=True)
        #   act.strengthening = simplify(cdSimplifyE(And(act.strengthening, step_wpc)).as_expr(), local_ctx=True)
        #   if DBG2: print('act.strengthening\n', step_wpc)
        if hasattr(model, "step_invariant") and not (model.step_invariant == True):
          step_wpc = Implies(And(act.precNode.invariant, act.actionPred, model.step_invariant), 
                             model.step_invariant)
          step_wpc = ForAll(postNode.postVars, step_wpc)
          step_wpc = simplify(cdSimplifyE(step_wpc).as_expr(), local_ctx=True)
          act.strengthening = simplify(cdSimplifyE(And(act.strengthening, step_wpc)).as_expr(), local_ctx=True)
          if DBG2: print('act.strengthening\n', step_wpc)
        # else:
        # wp = Implies(act.actionPred, stateInvDeltaX)
        wp = Implies(And(act.actionPred, step_wpc), stateInvDeltaX)
        wp = ForAll(postNode.postVars + temp_vars, wp)
        if DBG2: print('raw wpc:\n', wp)
        # wp = simplifyAndQE(wp)
    else: #not using the postNode's postvars but its regular pre vars
        postNodeInv = postNode.invariant
        # if not is_true(postNode.invariant):
        #     postNodeInv = substitute(postNode.invariant, postNode.subst)
        wp = Implies(act.actionPred, postNodeInv)
        if hasattr(model, "step_invariant") and not (model.step_invariant == True):
        #   step_wp = ForAll(postNode.postVars, 
        #                     Implies(act.actionPred, model.step_invariant))
          step_wp = Implies(act.actionPred, model.step_invariant)
          if DBG2: print('step_wpc\n', step_wp)
          #postNode's vars includes both its pre and post vars if the effect of the action is to 
          #change the post node's state
          wp = ForAll(postNode.vars + temp_vars, And(wp, step_wp))
        else:
          wp = ForAll(postNode.vars + temp_vars, wp)
        if DBG2: print('raw wpc:\n', wp)
    wp = simplifyAndQE(wp)
        #OLD: wp = ForAll(postNode.vars, Implies(act.actionPred, postNodeInv))
    return wp


'''does U <- U && wpc, optimzed as res(Inv, U && wpc) unless res(Inv, U && wpc) adds nothing to U && Inv'''
def updCtrlPred(act, node, wpc):
  global moreWork           #letting python know moreWork below is a global
  stateInv = node.invariant
  # ctrlPred = getCtrlPred(model, act)
  ctrlPred = act.controlPred
  print('guard of', act.name, ':\n', ctrlPred)
  newActGuard = simplify(And(ctrlPred, wpc)) 
  if DBG2: print("new unoptimized guard:\n", newActGuard)
  newActGuard = simplify(residue(stateInv, newActGuard).as_expr())
  print("newActGuard (simplified residue wrt inv):\n", newActGuard)
  # Compute difference between newActGuard and current guard to see if control pred needs updating:
  newActGuardDelta = residue(And(ctrlPred, stateInv), newActGuard)
  print("newActGuardDelta (residue of NewActGuard):", newActGuardDelta)
  if(len(newActGuardDelta) > 0):  
      act.controlPred = newActGuard
      # ctrlPred = newActGuard
      # ctrlPred = getCtrlPred(model, newActGuard)
      #print("changed guard:")
      moreWork = True
  return act.controlPred

def updateGuardDisj(guardDisjunction, act, guard):
  #***not sure about this, need to revisit***, see comment in the paper in this section
  # the guard of the action is actually a comb of a true guard and an assumption about the env. need to remove out those assumption terms when determining how to strengthen the inv. eg a>10 /\ x=2, the true guard is just x=2
#   if 'assumpVars' in act._fields and not isEmpty(act.assumpVars):
  if hasattr(act, 'assumpVars') and not isEmpty(act.assumpVars):
    # effective_guard = getGuard(act, node.vars + act.assumpVars, model)
    # effective_guard = getGuard(act)
    effective_guard = guard
    #*TBD: why isn't this used?
    actual_updated_guard = getConjNotContaining(effective_guard, act.assumpVars)
    if DBG2: print('updated guard without assumption:\n' + str(actual_updated_guard))
  else:
    # effective_guard = getGuard(act)
    effective_guard = guard
    # updated_guard = getGuard1(new_act_pred, node.vars) #was effective_guard
  
  #now use the (possibly) updated guard
  guardDisjunction = simplify(Or(guardDisjunction, effective_guard), local_ctx=True)
  # guardDisjunction = simplify(Or(guardDisjunction, guard), local_ctx=True)
  # print("updated guardDisjunction:\n" + str(guardDisjunction))
  return guardDisjunction

def mkSomeGuardHolds(node, guardDisjunction):
  if DBG2: print("guardDisjunction:\n" + str(guardDisjunction))
  someGuardHolds = simplifyAndQE(guardDisjunction)  # eliminate quantifiers and then simplify
  if DBG2: print("guardDisjunction after QE and simp:\n" + str(someGuardHolds))
  if someGuardHolds == False: 
      response = input("No guard holds. Do you wish to continue? [y/n]")
      assert response == 'y', "Exiting. Current someGuardHolds is " + str(someGuardHolds) 
  return someGuardHolds

# this is ensuring Inv -> someGuardHolds impl as Inv(s) := Inv(s) /\ someGuardHolds
# but optimzed so only update if changed
def updateInvariant(node, someGuardHolds, invDelta):
  stateInv = node.invariant
  # Compute difference between curr Inv and what's required for some guard true b/c new inv needs to be strong enough to establish someGuard
  print("going to calc inv delta as residue of stateInv and someGuardHolds..")
  newInvDeltaTemp = simplify(residue(stateInv, someGuardHolds).as_expr(), local_ctx=True)
  #print("newInvDelta:", newInvDelta)
  #print("verf check:", verfEquiv(newInvDelta0,newInvDelta))
  '''only update NewInvDelta if there is a change'''
  if newInvDeltaTemp == False: 
      response = input("current invariant contradicts guard disjunction. Do you wish to continue? [y/n]")
      assert response == 'y', "Invariant refinement failed. Exiting. Current Inv is " + str(stateInv)
      newInvDelta = invDelta
  if(newInvDeltaTemp == True):  
      print("no change to invariant on", node.name)
      newInvDelta = invDelta
  else:
      newInv = cdSimplifyE(And(stateInv, newInvDeltaTemp)).as_expr()
      #print("Invariant refinement disallows:")
      # print('checking invariant implication')
      #Q: This is what used to be but why would the old inv be stronger than new one? 
      # verifyImplies(stateInv, newInv)      
      verfImpl(newInv, stateInv)       
      node.invariant = newInv
      print("new invariant=\n" +  str(node.invariant))
      global moreWork; moreWork = True
      newInvDelta = newInvDeltaTemp
  return newInvDelta

'''update the controlpred on each arc to account for the strenghened inv''' 
def updateCtrlPreds(stateInv):
    for actIndex in range(len(transitions)):
        act = transitions[actIndex]
        #print("simplifying guard of", act['name'])
        ctrlPred = act.controlPred
        #print("actGuard:", actGuard)
        res = residue(stateInv, ctrlPred).as_expr()
        #print("newActGuard:", newActGuard)
        ctrlPred = simplify(And(ctrlPred, res), local_ctx=True)
        act.controlPred = ctrlPred
        if DBG2: print("updated control pred on action", act.name, "\n", act.controlPred)

def wrapWithCtrl(act, formula):    #U has already been strengthened Paper has U -> wcp + \E u. U
    # wpc = mkWPC(act)
    # print("wpc (weakest precond):\n", formula)
    f = formula
    if hasattr(act.precNode, 'controlVars'): print("***WARNING: ignoring control vars on the node", act.precNode.name)
    if hasattr(act, 'controlVar'): print("***WARNING: \"controlVar\" attribute is now \"controlVars\"")  
    if hasattr(act, 'controlVars') and act.controlVars != []: 
        # formula = updGuard(act, act.precNode, formula)
        f = Exists(act.controlVars, formula)   #SN: \E u. U /\ wpc
    print("ctrl wrapped formula:\n", f)
    f = simplifyAndQE(f)
    # if DBG2: print('ctrl wpc after simp and QE =\n' + str(wpc))
    return f

def wrapWithEnv(act, node, formula):
  if hasattr(node, 'envVars') and not isEmpty(node.envVars):
      formula = ForAll(node.envVars, Implies(node.envPred, formula))
  elif hasattr(act, 'envVars') and not isEmpty(act.envVars):
      formula = ForAll(act.envVars, Implies(act.envPred, formula))
  else:
      if DBG2: print("No env vars on node", node.name, "or action", act.name)
  print("env wrapped formula:\n", formula)
  formula = simplifyAndQE(formula)
  return formula


""" ---------- next 3 funs basically only used for non-synth arcs, ie. those that are triggered by the env in an Assume-Guarantee setting -------------"""
def mkWPToEnsureAnyTgtTransIsValid(act, node):
  all_wps_4_cmpt_transs = True
  for a in transitions:
    #this 'ere is checking that start node of the arc is the tgt node and that arc is a nosynth arc
    # if ('noSynth' in act._fields and a.noSynth):
    if hasattr(act, 'noSynth') and a.noSynth:
      print('\n---- targetting arc', a.name)
      tgt_act_tgt_node = a.postNode
      wp4vti = mkWPForEnsuringTargetImplication(act, node.vars, a, tgt_act_tgt_node.vars)
      print('wp4vti =\n',wp4vti)
      #wp4vti is actually a list, the * turns a [] list into an argument list
      wp4vti = simplify(And(*cdSimplifyE(wp4vti))) 
      print('simpl wp4vti =\n',wp4vti)
      #AND b/c you need to ensure that the arbiter action ensures the correctness of any component trans that is otherwise enabled           
      all_wps_4_cmpt_transs = And(all_wps_4_cmpt_transs,wp4vti)
  return all_wps_4_cmpt_transs

#construct \A s'. act(s,s') -> (G(s') -> \A s''. tgt_act(s',s'') -> L(s''))
def mkWPForEnsuringTargetImplication(act,state_vars,tgt_act,tgt_node_state_vars): 
    tgt_implc = mkTargetImplication(tgt_act, tgt_node_state_vars)
    if DBG2: print("tgt impl =\n"+ str(tgt_implc))
    post_node = act.postNode
    post_tgt_implc = substitute(tgt_implc, post_node.subst)
    et2svi = ForAll(post_node.postVars, Implies(act.actionPred, post_tgt_implc))
    print('CondForEnsuringTargetImplication=\n',et2svi)
    et2svi = simplifyAndQE(et2svi)
    return et2svi
    
#This is G(s) -> L(s') as opposed to strengthening the guard w/ wcp (used for non synth edges)
def mkTargetImplication(act,state_vars): 
    wcp = mkWPC(act)
    wcp = simplifyAndQE(wcp)
    guard = getGuard(act, state_vars, model)
    impl = Implies(guard,wcp)
    impl = simplify(impl)
    return impl

#--------------------------- main --------------------------------------
# moved to top of file: moreWork = True  #declaring a global
# model refinement solver - for multinode models where nodes may have more than one outarc
# TODO:  initially, simplify each transition wrt the state invariant
def mr(): #(model, initProps, safetyProps):
    print("Refining Model", model.name)

    # initial state Properties: what should this do? SN: initialState is unused
    # initialState = True
    # for initProp in initProps:
    #     print("Localizing initial state with initial state property:", initProp)
    #     f0 = simplify(And(initialState,initProp), local_ctx=True)   #print(f0)
    #     initialState = cdSimplifyE(f0).as_expr()
    # #printState(initialState)

    initInvsWithSafetyProps()

    # fixpoint iteration loop
    iterCnt = 0
    global moreWork
    while (moreWork and iterCnt <= 50):
        moreWork = False
        print("\n----------------\niteration", iterCnt)
        print("Current Model")
        printModel(model)
        iterCnt = iterCnt + 1

        # refine each node invariant wrt its out-arcs and post-state prop
        for node in nodes:  
            print("\n------- Refining the state invariant for node", node.name)
            # state_inv = node['invariant']
            guardDisjunction = False
            node_has_an_outgoing_arc = False
            for act in transitions:
                node_has_an_outgoing_arc = True
                stateInv = node.invariant
                if act.precNode == act.postNode: #otherwise stateInvDelta is not used
                    stateInvDeltaX = substitute(node.stateInvDelta, node.subst)
                else:
                    stateInvDeltaX = None
                if act.precNode.name == node.name: #and 
                  print('\n--- Arc', act.name)
                  #have to do it this way, using "implies" fn causes python to evaluate both args first
                  if not hasattr(act, 'noSynth') or not act.noSynth:
                      guard,ctrlPred = mkNewGuard(act, node, stateInvDeltaX)
                      if DBG2: print('guard:\n' + str(guard))
                      # if DBG2: print('guard:\n', getGuard(act))
                  #this needed to update the invariant, next
                  guardDisjunction = updateGuardDisj(guardDisjunction, act, guard)
                  print("updated guardDisjunction:\n" + str(guardDisjunction))
            if node_has_an_outgoing_arc:
                print('\n----- Completed arcs from node ' + node.name + '. Now checking if invariant and guards needs updating')
                someGuardHolds = mkSomeGuardHolds(node, guardDisjunction)
                node.stateInvDelta = updateInvariant(node, someGuardHolds, node.stateInvDelta)
                #update the ctrl preds a 2nd time on each of the arcs by forming residue wrt to new invar
                # updateGuards(node.invariant)
                updateCtrlPreds(node.invariant)
            else: print('No refinement. Node is terminal')  #Q: when would this occur?

    if not moreWork:
        print("\n----------------\nFinal Model - fixpoint at iteration", iterCnt)
    else:
        print("\n****************\nWarning: Non-fixpoint Model - after iteration", iterCnt)
    printModel(model)


# This generator assume that the model is a fixpoint (so the invariants are inductive).
def generateControlStrategyByCases(model):
    print("Generating Control Strategy by Cases")
    codeFile = open(model.name + "controlFun.py", "w")
    for act in model.transitions:
        if is_and(origControlPreds[act.name]) and act.controlVars != []:
            codeFile.write("def controlFn(")
            needSep = False
            for param in act.precNode.vars:
                if needSep == True:
                    codeFile.write(",")
                else: needSep = True
                codeFile.write(str(param))
            codeFile.write("):\n\t")
            print("act", act.name, "has original bounds on controlPred of", origControlPreds[act.name])
            # preStateInv = act.precNode.invariant

            bounds = getBounds(act.controlVars, origControlPreds[act.name])
            # bounds = [0,4]; print("***ASSUMING FIXED BOUND!!")
            if bounds == None:
                break
            print("bounds:", bounds)
            # wcps = t0(makeWeakestControllablePredecessor(act))[0].as_expr()
            # print("wcps:", wcps)
            # NodeInv = act.precNode.invariant
            # print("NodeInv",NodeInv)
            for uval in range(bounds[0], bounds[1]):
                #print("uval", uval, is_int(uval), is_int(IntVal(uval)))
                uCase = act.controlVars[0] == IntVal(uval)
                print("uCase", uCase)
                envelope = substitute(act.controlPred, (act.controlVars[0], IntVal(uval)))
                envelope = simplify(envelope, local_ctx=True)
                print("envelope", envelope)
                codeFile.write("if ") 
                codeFile.write(str(envelope)) #.to_string())
                codeFile.write(":\n") 
                codeFile.write("\t\treturn " + str(IntVal(uval)) + "\n")
                codeFile.write("\telse ")
            codeFile.write("return " + str(bounds[1]) + "\n")
    codeFile.close()


# invoke model refinement on the model
mr() #(model, initProps, safetyProps)  # for models where each node has at most one outarc



# assume: uConstraint has the form And(lb <= u, u <= ub) UNUSED
def getBounds(us, uConstraint):
    result = []
    # assert len(us) == 1, "getBounds currently expects a single control variable"
    if len(us) != 1:
        print("***getBounds currently expects a single control variable. Not generating a control function for this action")
        return None
    u = us[0]
    # print("u:", u, "|", uConstraint)
    # assert is_int(u), "u must be an integer"
    if not is_int(u): 
        print("***u must be an integer. Not generating control function for this action")
        return None
    for ineq in uConstraint.children():
        if u == ineq.children()[0]:
            result.append(ineq.children()[1].as_long())
            # print(result)
    if result[0] > result[1]:
        return [result[1], result[0]]   #flip the bounds
    else:
        return result

# choose a control strategy generator
#controlStrategy = generateControlStrategyBySMT(model)
controlStrategy = generateControlStrategyByCases(model)

