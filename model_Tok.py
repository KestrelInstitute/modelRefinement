# model of Tokeneer system
# python model_Tok.py
from z3 import *

# types
Time = IntSort()

clock,k = Consts('clock k', Time)  # k>=0, clock=now >= 0.

# player inputs:  degenerate in this example
e, u   = Consts('e u', IntSort())

# State variables
locked, token, open    = Consts('locked token open', BoolSort())
locked1, token1, open1 = Consts('locked1 token1 open1', BoolSort())  #post-state vars

# FD vars introduced by property normalization
lastInsert, lastInsert1   = Consts('lastInsert lastInsert1',Time)
lastUnlock, lastUnlock1   = Consts('lastUnlock lastUnlock1',Time)
unlockTimer, unlockTimer1 = Consts('unlockTimer unlockTimer1',Time)

state       = [open, token, locked, lastInsert, lastUnlock, unlockTimer]
state1      = [open1, token1, locked1, lastInsert1, lastUnlock1, unlockTimer1]
subst       = [(open,open1),(token,token1),(locked,locked1),
               (lastInsert,lastInsert1), (lastUnlock,lastUnlock1),
               (unlockTimer,unlockTimer1)]
stateInv    = And(0<=k, 0<=clock)

# Actions/Transitions/Events: 
# Controllable/Sys: 
# Uncontrollable/Env:

removeAct = {'name'         :"removeAct",
             'actionPred'   :And(token==True, token1==False,
                                 locked == locked1, open == open1,
                                 lastInsert == lastInsert1,
                                 lastUnlock == lastUnlock1,
                                 unlockTimer == unlockTimer1),
             'controllable' :False,
             'envVar'       : [],
             'envPred'    :True,
             'controlVar' : [],
             'controlPred':True}

insertAct = {'name'         :"insertAct",
             'actionPred'   :And(token==False, token1==True,
                                 locked == locked1, open == open1,
                                 #lastInsert == lastInsert1,
                                 lastUnlock == lastUnlock1,
                                 unlockTimer == unlockTimer1),
             'controllable' :False,
             'envVar'       : [],
             'envPred'      :True,
             'controlVar'   : [],
             'controlPred'  :True}

lockAct   = {'name'         :"lockAct",
             'actionPred'   : And(locked==False, locked1==True,
                                 token == token1, open == open1,
                                 lastInsert == lastInsert1,
                                 lastUnlock == lastUnlock1,
                                 unlockTimer == unlockTimer1),
             'controllable' :True,
             'envVar'       : [],
             'envPred'      : True,
             'controlVar'   : [],
             'controlPred'  :True}

unlockAct = {'name'         :"unlockAct",
             'actionPred'   :And(locked==True, locked1==False,
                                 token == token1, open == open1,
                                 lastInsert == lastInsert1),
             'controllable' :True,
             'envVar'       : [],
             'envPred'      :True,
             'controlVar'   : [],
             'controlPred'  :True}

transitions = [removeAct, insertAct, unlockAct, lockAct]

# Initial Properties
initialProp0 = (open==False)
initialProp1 = (token==False)
initialProp2 = (locked==True)
initialProp3 = (unlockTimer == -1)              # effectively -oo
initialProp4 = (lastInsert  == -1)              # effectively -oo
initialProp5 = (lastUnlock  == -1)              # effectively -oo

# Safety Properties
safetyProp0 = Implies(insertAct['actionPred'], lastInsert1  == clock)  # FD 
safetyProp1 = Implies(insertAct['actionPred'], unlockTimer1 == clock)  # FD (hmm, same as lastInsert1...)
safetyProp2 = Implies(unlockAct['actionPred'], lastUnlock1  == clock)  # FD

# [] Unlock => <->_k Insert  (may unlock after insert)
safetyProp3 = Implies(unlockAct['actionPred'], (clock <= (lastInsert + k)))

# [] Insert => <>_k Unlock  (must unlock after insert)
# this is the critical property - it forces the Unlock action
safetyProp4 = Implies(unlockTimer > lastUnlock, clock - unlockTimer <= k)  

initProps   = [initialProp0, initialProp1, initialProp2, initialProp3, initialProp4, initialProp5]
safetyProps = [safetyProp0, safetyProp1, safetyProp2, safetyProp3, safetyProp4]
