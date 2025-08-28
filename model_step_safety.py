from z3 import *

x,xX = Ints('x xX')
subst = [(x, xX)]
state = [x]
state1 = [xX]
stateInv = x == x

double_x = {'name'         :"double",
            'actionPred'   : xX == 2*x,
            'controllable' :False,
            'envVar'       : [],
            'envPred'    :True,
            'controlVar' : [],
            'controlPred':True}

halve_x = {'name'         :"halve",
            'actionPred'   : xX == x/2,
            'controllable' :False,
            'envVar'       : [],
            'envPred'    :True,
            'controlVar' : [],
            'controlPred':True}

transitions = [double_x, halve_x]
initialProps = []
initProps = []
safetyProps = [xX >= x]