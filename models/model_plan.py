# example model input to planner planner generator (which generates constraints that are then inserted by the planner generator into the planner). An entire mission is modeled as a macro action, rather than the individual activities, using constant expressions for the intermediate values such st2, dur2, etc.
'''
TBD
'''
from z3 import *
# from collections import namedtuple
from types import SimpleNamespace

'''--- TYPES ---'''
#not using namedtuples b/c they aren't mutable

''' --- CONSTANTS ---'''
# later, create a resource class to hold this
SPEED = 1 # km/hr. this is resource specific constant
FUEL_RATE =  1 # litres/km. this is resource specific constant

'''--- STATE VARIABLES ---'''
# SVC_T, SVC_D, SVC_L, BASE = Ints('SVC_T SVC_D SVC_L BASE')
SVC_T, SVC_D, AVAIL = Ints('SVC_T SVC_D AVAIL')
svc_t, svc_d, avail = Ints('svc_t svc_d avail')
activity, fuel = Ints('activity fuel')
st, orig, dest = Ints('st orig dest')
activityX, fuelX = Ints('activityX fuelX')
stX, origX, destX = Ints('stX origX destX')
dur1, dur3, dur5 = Ints('dur1 dur3 dur5')
st3, st5 = Ints('st3 st5') 
state = [st]; stateX = [stX]
subst = list(zip(state, stateX)) #+ [(dur3,dur3X), (dur1,dur1X)]

'''--- UTILS ---'''
time_to_svc_l = IntVal(1) #  TBD: use a distance function d()/SPEED

'''---------- MAIN ---------'''
singleton = SimpleNamespace(
  name = 'singleton',
  vars = state, 
  envVars = [svc_t, svc_d, avail], 
  envPred = And(svc_t == SVC_T, svc_d == SVC_D, avail == AVAIL), 
  tempVars = [st3, st5],           #not true vars, equivalent to #defines
  postVars = stateX,
  subst = subst,
  invariant = True,
  stateInvDelta = True      #for optimizing the calculation of the wpc, can be anything
  )

macro_action = SimpleNamespace( 
  name = "mission idle --> idle_f",
  actionPred = And( st3 == st + dur1 + time_to_svc_l,
                    st5 == st3 + dur3 + time_to_svc_l, 
                    stX == st5 + dur5
                  ),
  controlVars = [dur1, dur3, dur5],
  controlPred = And(dur1 >= 0, dur3 >= 0, dur5 >= 0),#, st5 >= 0),
  precNode = singleton,
  postNode = singleton,
  strengthening = True
  )

model = SimpleNamespace(
  name = 'Planning metametamodel',
  nodes = [singleton],
  transitions = [macro_action], 
  DOING_FORALL_EXISTS = True,                 #should this just be a global?
  # although Z3 automatically treats these as consts, isNodePred needs to know what they are
  constants = [SPEED, FUEL_RATE],
  externals = [SVC_T, SVC_D, AVAIL],
  step_invariant = True       #step_inv is to step prop as node inv is to safety prop
)

# Required Properties
initProps = []

#should be called nodeProps, but name retained for legacy reasons
safetyProps = \
  [
    st >= 0, dur3 == SVC_D, st3 == SVC_T, AVAIL <= st
  ]

""" Step prop b/c a transition does not take place unless dur3 and st3 have these values. Was originally a state prop but that doesn't work b/c L(s') was trying to use the current iteration's value of dur3 and st3. Instead we want to say that dur3 st3 only get assingned their satisfying values if the action is taken. """
# stepProps = \
#   [dur3 == SVC_D, st3 == SVC_T, AVAIL <= st]

if __name__ == "__main__": 
   print('model', model)
  #  print('\nsafety props', safetyProps(0, 0, 0, 0, 0))
