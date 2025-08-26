from z3 import *
from collections import namedtuple
from types import SimpleNamespace

# Model = namedtuple('Model', ['name', 'nodes', 'transitions', 'step_invariant'])

x,xX = Reals('x xX')
state = [x]
stateX = [xX]
subst = [(x, xX)]
# stateInv = x == x


singleton = SimpleNamespace(
  name = "singleton",
  vars = state,
  state_vars = state, 
  controlVar = [],
  envVar = [],
  envPred = True,
  tempVars = [],
  tempPred = True,
  postVars = stateX,
  subst = subst,
  invariant = True
  )

double_x = SimpleNamespace(
  name         ="double",
  actionPred   = xX == 2*x,
  precNode = singleton,
  postNode = singleton)

halve_x = SimpleNamespace(
  name         ="halve",
  actionPred   = xX == x/2,
  precNode = singleton,
  postNode = singleton)

model = SimpleNamespace(
  name = "step property example",
  nodes = [singleton],
  transitions = [double_x, halve_x], 
  step_invariant = True
)

# transitions = [double_x, halve_x]
# initialProps = []
initProps = []
safetyProps = [xX >= x]