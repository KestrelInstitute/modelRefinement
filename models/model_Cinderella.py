# model of Cinderella-Stepmother problem (c==3, see Older_V3 for c==2 model and results). System starts in mS, stepmother plays first, then its in node mC and its Cinderellas turn, then back to mS, etc. b0S and b0C, etc represent the state of the bucket b0, the S or C simply indicates it value in the given node. The transition reln assigns the "post" values to them based on the transition relation, b0C is the post value when in mS and b0S its post value when in mC

from z3 import *
from types import SimpleNamespace

# bucket capacity
c = RealVal(3.0)  # creates a Z3 real constant with value 3.0

#  state  variables
b0S, b0C = Reals('b0S b0C')
b1S, b1C = Reals('b1S b1C')
b2S, b2C = Reals('b2S b2C')
b3S, b3C = Reals('b3S b3C')
b4S, b4C = Reals('b4S b4C')
#turn, turn1 = Ints('turn turn1')
stateS     = [ b0S, b1S, b2S, b3S, b4S]
stateC     = [ b0C, b1C, b2C, b3C, b4C]
# subst      = [(b0S,b0C), (b1S,b1C),(b2S,b2C),(b3S,b3C), (b4S,b4C),(c,cC)] 
mSInv  = And( 0 <= b0S, 0 <= b1S, 0 <= b2S, 0 <= b3S, 0 <= b4S)
mCInv  = And( 0 <= b0C, 0 <= b1C, 0 <= b2C, 0 <= b3C, 0 <= b4C)

# Env, Sys Control variables
e0,e1,e2,e3,e4 = Reals('e0 e1 e2 e3 e4')
u = Int('u')  # Cinderella choice of bucket: u, (u+1)%5

# Nodes
mS  = SimpleNamespace(
    name='mS',
    vars=stateS,  # [b0S,b1S, b2S, b3S, b4S, c],
    # postVars     = stateC,    # optional= for self transitions
    # subst        = subst,
    invariant=mSInv
)
mC  = SimpleNamespace(
    name='mC',
    vars=stateC,  # [ b0C, b1C, b2C, b3C, b4C, cC],
    # postVars     = stateC,    # optional= for self transitions
    # subst        = subst,
    invariant=mCInv
)

# Arcs/Transitions
StepAction = SimpleNamespace(
    name="stepmother",
    actionPred=And(
        b0C == b0S+e0, b1C == b1S+e1, b2C == b2S+e2, b3C == b3S+e3, b4C == b4S+e4,
        b0C + b1C + b2C + b3C + b4C == b0S + b1S + b2S + b3S + b4S + 1.0
        # cC == c
    ),
    envVars=[e0, e1, e2, e3, e4],
    envPred=And(
        0.0 <= e0, 0.0 <= e1, 0.0 <= e2, 0.0 <= e3, 0.0 <= e4,
        e0 + e1 + e2 + e3 + e4 == 1.0
    ),
    controlVars=[],
    controlPred=True,
    precNode=mS,
    postNode=mC
)

CindAction = SimpleNamespace(
    name="cinderella",
    actionPred=And(
        Implies(u==0, And(b0S == 0, b1S == 0, b2C == b2S, b3C == b3S, b4C == b4S)),
        Implies(u==1, And(b0C == b0S, b1S == 0, b2S == 0, b3C == b3S, b4C == b4S)),
        Implies(u==2, And(b0C == b0S, b1C == b1S, b2S == 0, b3S == 0, b4C == b4S)),
        Implies(u==3, And(b0C == b0S, b1C == b1S, b2C == b2S, b3S == 0, b4S == 0)),
        Implies(u==4, And(b0S == 0, b1C == b1S, b2C == b2S, b3C == b3S, b4S == 0))
        # cC == c
    ),
    envVars=[],
    envPred=True,
    controlVars=[u],
    controlPred=And(0 <= u, u <= 4),
    precNode=mC,
    postNode=mS
)

nodes       = [mS, mC]
transitions = [StepAction, CindAction]
model       = SimpleNamespace(
    name='Cinderella',
    initNode=mS,
    nodes=[mS, mC],
    transitions=[StepAction, CindAction]
)
    
# Required Properties
initProps   = [b0S  == 0, b1S  == 0, b2S  == 0, b3S  == 0, b4S  == 0,
               b0C == 0, b1C == 0, b2C == 0, b3C == 0, b4C == 0, c == 3.0]
safetyProps = [c >= b0S, c >= b1S, c >= b2S, c >= b3S, c >= b4S,
               c >= b0C, c >= b1C, c >= b2C, c >= b3C, c >= b4C]