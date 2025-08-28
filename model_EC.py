# model of an Elevator Control System
from z3 import *

# State variables (vars plus their primed version: x, x1)
floorA, floorA1 = Consts('floorA floorA1', BoolSort())
floorB, floorB1 = Consts('floorB floorB1', BoolSort())
floorC, floorC1 = Consts('floorC floorC1', BoolSort())

state    = [floorA, floorB, floorC]
stateInv = And()
subst    = [(floorA, floorA1), (floorB, floorB1), (floorC, floorC1)]
state1   = [floorA1, floorB1, floorC1]

# Task representations
buttonA, buttonA1 = Consts('buttonA buttonA1', BoolSort())
buttonB, buttonB1 = Consts('buttonB buttonB1', BoolSort())
buttonC, buttonC1 = Consts('buttonC buttonC1', BoolSort())

# Initial Properties
initialProp0 = And(floorA,Not(floorB), Not(floorC))
initialProp1 = And(Not(buttonA), Not(buttonB), Not(buttonC))
initProps    = [initialProp0, initialProp1]

# Actions/Transitions/Events: 

PushA     = {'name'         : "PushA",  # push button on floor A
             'actionPred'   : And(buttonA1 == True, buttonB1 == buttonB, buttonC1==buttonC,
                                  floorA1==floorA, floorB1==floorB, floorC1==floorC ),
             'controllable' : False,  # Env action
             'envVar'       : [buttonA, buttonB, buttonC],
             'envPred'      : And(),
             'controlVar'   : [],
             'controlPred'  : And()}

PushB     = {'name'         : "PushB",  # push button on floor B
             'actionPred'   : And(buttonA1 == buttonA, buttonB1 == True, buttonC1==buttonC,
                                  floorA1==floorA, floorB1==floorB, floorC1==floorC),
             'controllable' : False,  # Env action
             'envVar'       : [buttonA, buttonB, buttonC],
             'envPred'      : And(),
             'controlVar'   : [],
             'controlPred'  : And()}

PushC     = {'name'         : "PushC",  # push button on floor C
             'actionPred'   : And(buttonA1 == buttonA, buttonB1 == buttonB, buttonC1==True,
                                  floorA1==floorA, floorB1==floorB, floorC1==floorC),
             'controllable' : False,  # Env action
             'envVar'       : [buttonA, buttonB, buttonC],
             'envPred'      : And(),
             'controlVar'   : [],
             'controlPred'  : And()}

upA         = {'name'         : "upA",  # move from floorA to FloorB
              'actionPred'   : And(floorA, Not(floorA1), floorB1, floorC1==floorC, 
                                   buttonA1 == False, buttonB1 == buttonB, buttonC1==buttonC), # or buttonB1==False?
              'controllable' : True,  # Sys action
              'envVar'       : [],
              'envPred'      : And(),
              'controlVar'   : [],
              'controlPred'  : And()}

upB         = {'name'         : "upB",  # move from floorB to FloorC
              'actionPred'   : And(floorA1==floorA, floorB, Not(floorB1), floorC1,
                                   buttonA1 == buttonA, buttonB1 == False, buttonC1==buttonC),
              'controllable' : True,  # Sys action
              'envVar'       : [],
              'envPred'      : And(),
              'controlVar'   : [],
              'controlPred'  : And()}

dnC        = {'name'         : "downC",  # move from floorC to FloorB
              'actionPred'   : And(floorA1==floorA, floorB1, floorC, Not(floorC1),
                                   buttonA1 == buttonA, buttonB1 == buttonB, buttonC1==False),
              'controllable' : True,  # Sys action
              'envVar'       : [],
              'envPred'      : And(),
              'controlVar'   : [],
              'controlPred'  : And()}

dnB        = {'name'         : "downB",  # move from floorB to FloorA
              'actionPred'   : And(floorA1, floorB, Not(floorB1), floorC1==floorC,
                                   buttonA1 == buttonA, buttonB1 == False, buttonC1==buttonC),
              'controllable' : True,  # Sys action
              'envVar'       : [],
              'envPred'      : And(),
              'controlVar'   : [],
              'controlPred'  : And()}

transitions = [PushA, PushB, PushC, upA, upB, dnC, dnB]

# Safety Properties
# at most one floor at a time
safetyProp0 = And(Not(And(floorA,floorB)), Not(And(floorB,floorC)), Not(And(floorA,floorC)))

# possible invariant to enforce task management actions
# [] floorA => not buttonA, [] floorB => not buttonB, [] floorC => not buttonC

#safetyProps = [safetyProp0,safetyProp1,safetyProp2,safetyProp3,safetyProp4,safetyProp5]
safetyProps = [safetyProp0]

# Response Property:
# [] buttonA => <> floorA, [] buttonB => <> floorB, [] buttonC => <> floorC 
