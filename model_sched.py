# model of simple scheduling problem from
# Altisen et al. "A framework for scheduler synthesis"
# in IEEE Real-Time Systems Symposium (1999), pp. 154-163.
from z3 import *

# types
Time = IntSort()

# Env inputs:  degenerate in this example
dura,durb   = Consts('dura durb', IntSort())
duraBounds  = And(5<=dura, dura<=7)
durbBounds  = And(3<=durb, durb<=4)

# State variables: start times for tasks a and b
sta, sta1 = Consts('sta sta1', IntSort())
stb, stb1 = Consts('stb stb1', IntSort())
state       = [sta, stb]
state1      = [sta1, stb1]
subst       = [(sta,sta1),(stb,stb1)]
stateInv    = And(0<=sta, 0<=stb)

# Nodes
m0  = {'name'         : 'm0',
       'vars'         : state,
       'invariant'    : True}

# Actions/Transitions/Events: 
choose = {'name'         : "choose",
          'actionPred'   : And(sta1 == sta, stb1 == stb),
          'controllable' : True,
          'envVar'       : [dura,durb],
          'envPred'      : And(duraBounds, durbBounds),
          'controlVar'   : [sta, stb],
          'controlPred'  : True,
          'precNode'   :m0,
          'postNode'   :m0 }

transitions = [choose]

# Initial Properties
initialProp0 = And(sta >= 0, stb >= 0)

# Safety Properties
safetyProp0 = (sta + dura <= 12)
safetyProp1 = (stb + durb <= 25)
safetyProp2 = 14 <= stb
safetyProp3 = (stb + durb <= sta + dura + 10)

initProps   = [initialProp0]
safetyProps = [safetyProp0, safetyProp1, safetyProp2, safetyProp3]
