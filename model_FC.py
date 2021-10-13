# model of discrete packet flow control system

from z3       import *

#  state  variables
buf, buf1 = Ints('buf buf1')
out, out1 = Ints('out out1')
state       = [buf, out]
state1      = [buf1,out1]
subst       = [(buf,buf1),(out,out1)]
stateInv    = And(0 <= buf, 0 <= out)

# Env, Sys Control variables
e,u = Ints('e u')

# Nodes
m0  = {'name'         : 'm0',
       'vars'         : [buf,out],
       'invariant'    : True}

# Arcs/Transitions
updateAction = {'name'       :"update",
                'actionPred' :And(buf1 == buf + e - out, out1 == out + u),
                'envVar'     :[e],
                'envPred'    :And(0 <= e, e <= 4),
                'controlVar' :[u],
                'controlPred':And(-1 <= u, u <= 1),
                'precNode'   :m0,
                'postNode'   :m0}
transitions = [updateAction]

# Required Properties
initProps   = [buf == 0, out == 0]
safetyProps = [0 <= buf, buf <= 20, 0 <= out, out <= 4]
