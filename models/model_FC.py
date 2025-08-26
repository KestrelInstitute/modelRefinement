# model of discrete packet flow control system

from z3       import *
from types import SimpleNamespace

#  state  variables
buf, bufX = Ints('buf bufX')
out, outX = Ints('out outX')
state       = [buf, out]
stateX      = [bufX,outX]
subst       = [(buf,bufX),(out,outX)]
stateInv    = And(0 <= buf, 0 <= out) #SN: where is this used?

# Env, Sys Control variables
e,u = Ints('e u')

# Nodes
m0 = SimpleNamespace(
  name         = "main",
  vars         = [buf,out],
  postVars     = stateX,    # optional= for self transitions
  subst        = subst,     # optional= for self transitions
  invariant    = True,
  # stateInvDelta = True      #can be anything
)

# Arcs/Transitions
updateAction = SimpleNamespace(
    name       = "update",
    actionPred = And(bufX == buf + e - out, outX == out + u),
    envVars     = [e],
    envPred    = And(0 <= e, e <= 4),
    #the Or forms produce more long winded refined models
    # envPred    = Or(e == 0, e == 1, e == 2, e == 3, e == 4), 
    controlVars = [u],
    controlPred= And(-1 <= u, u <= 1),
    # controlPred= Or(u == -1, u == 0, u == 1), 
    precNode   = m0,
    postNode   = m0
)
transitions = [updateAction]

model = SimpleNamespace(
    name        = "FC",
    initNode    = m0,
    nodes       = [m0],
    transitions = transitions
)

# Required Properties
initProps   = [buf == 0, out == 0]
safetyProps = [0 <= buf, buf <= 20, 0 <= out, out <= 4]

#safetyProps= [out >= 0, out <= 4,
#              Not(buf + -1*out <= -1), Not(-1*buf + out <= -17),
#              -1*buf + 3*out <= 3,   buf + -3*out <= 11,
#              buf + -4*out <= 10,  -1*buf + 4*out <= 6]
#
#      out + u >= 0
#      out + u <= 4
#      Not(buf + -1*u + -2*out <= -1)
#      Not(-1*buf + u + 2*out <= -13)
#      Not(buf + -3*u + -4*out <= -4)
#      Not(-1*buf + 3*u + 4*out <= -8)
#      Not(-1*buf + 4*u + 5*out <= -7)
#      Not(buf + -4*u + -5*out <= -7)

# equivalent solution:
#         Not(buf + -4*u + -5*out <= -7),  Not(-1*buf + 4*u + 5*out <= -7),
#         -1 <= buf + -2*u + -3*out,       buf + -2*u + -3*out <= 9
