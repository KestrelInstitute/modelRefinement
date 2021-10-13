# model of a Readers-Writers system
from z3 import *

# State variables (vars plus their primed version: x, x1)
nr, nr1 = Consts('nr nr1', IntSort())
nw, nw1 = Consts('nw nw1', IntSort())

state    = [nr, nw]
stateInv = And(0 <= nr, 0 <= nw)
subst    = [(nr, nr1), (nw, nw1)]
state1   = [nr1, nw1]

# Env, Sys Control variables:  degenerate in this example

# Initial Properties
initialProp0 = (nr == 0)
initialProp1 = (nw == 0)
initProps    = [initialProp0, initialProp1]

# Nodes
m0  = {'name'         : 'm0',
       'vars'         : [nr, nw],
       'invariant'    : True}

# Arcs/Transitions
startRead = {'name'         :"startRead",
             'actionPred'   : And(nr1 == nr + 1, nw1 == nw),
             'controllable' : False,
             'envVar'       : [],
             'envPred'      :True,
             'controlVar'   : [],
             'controlPred'  :True,
             'precNode'   :m0,
             'postNode'   :m0}

endRead   = {'name'         :"endRead",
             'actionPred'   :And(nr > 0, nr1 == nr - 1, nw1 == nw),
             'controllable' :True,
             'envVar'       : [],
             'envPred'      :True,
             'controlVar'   : [],
             'controlPred'  :True,
             'precNode'   :m0,
             'postNode'   :m0}

startWrite = {'name'        :"startWrite",
             'actionPred'   :And(nw1 == nw + 1, nr1 == nr),
             'controllable' :False,
             'envVar'       : [],
             'envPred'      :True,
             'controlVar'   : [],
             'controlPred'  :True,
              'precNode'   :m0,
              'postNode'   :m0}

endWrite   = {'name'        :"endWrite",
             'actionPred'   :And(nw > 0, nw1 == nw - 1, nr1 == nr),
              'controllable' :True,
             'envVar'       : [],
             'envPred'      :True,
             'controlVar'   : [],
             'controlPred'  :True,
              'precNode'   :m0,
              'postNode'   :m0}

transitions = [startRead, endRead, startWrite, endWrite]

# Safety Property: [] ((nw = 0) ∨ (nw = 1 ∧ nr = 0))
safetyProp0 = Or(nw == 0, And(nw == 1, nr == 0))

safetyProps = [safetyProp0]
