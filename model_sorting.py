# model of sorting
# python model_sched.py
from z3 import *
from IntList import *

lst = Const('lst', IntList)

# variables: start times for tasks a and b
x0,x1,x2  = Consts('x0 x1 x2', IntList)
z0,z1,z2  = Consts('z0 z1 z2', IntList)

# These are the rewrite instances, but need the general equations + unification
IntListRewrites = [ #(ordered(nil), True),
    (ordered(concat(z1, z2)), And(ordered(z1), le(bag(z1),bag(z2)), ordered(z2))),
    (bag(concat(z1, z2)),  bag_union(bag(z1), bag(z2)))]

# Nodes
N0  = {'name'         : 'N0',
       'vars'         : [x0],
       'invariant'    : True}
N1  = {'name'         : 'N1',
       'vars'         : [x1,x2],
       'invariant'    : True}
N2  = {'name'         : 'N2',
       'vars'         : [z1,z2],
       'invariant'    : True}
N3  = {'name'         : 'N3',
       'vars'         : [z0],
       'invariant'    : True}

# Actions/Transitions/Events: 

decomp = {'name'         : "decomp",
          'actionPred'   : True,  # And(length(x)>length(x1), length(x)>length(x2)),
          'envVar'       : [x0],
          'envPred'      : True,
          'controlVar'   : [x1,x2],
          'controlPred'  : True,
          'preNode'      : N0,
          'postNode'     : N1
         }

fxf    = {'name'         : "fxf",
          'actionPred'   : And(bag(x1)==bag(z1), ordered(z1), bag(x2)==bag(z2), ordered(z2)),
          'envVar'       : [x1,x2],
          'envPred'      : True,
          'controlVar'   : [z1,z2],
          'controlPred'  : True,
          'preNode'      : N1,
          'postNode'     : N2
         }

comp   = {'name'         : "comp",
          'actionPred'   : z0 == concat(z1, z2),
          'envVar'       : [z1,z2],
          'envPred'      : True,
          'controlVar'   : [z0],
          'controlPred'  : True,
          'preNode'      : N2,
          'postNode'     : N3
         }

transitions = [comp,fxf,decomp]

# Initial Properties
initialProp0 = True

# Safety Properties
safetyProp = And(bag(x0)==bag(z0), ordered(z0))

initProps   = []
safetyProps = [safetyProp]
