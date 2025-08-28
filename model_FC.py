# model of flow control system
# state:List[Var], stateInv:Expression,
# subst:List[Pair(Expr,Expr)]
# transitions:List(Action),
# Action: Dictionary{name:String, actionPred:Expr,
#                    envVar:Expr, envPred:Expr,
#                    controlVar:Expr, controlPred:Expr}
# initProps:List(stateProperty), stateProps:List(stateProperty),
# safetyProps:List(ActionProperty)

from z3       import *

e,u = Ints('e u')
buf, buf1 = Ints('buf buf1')
out, out1 = Ints('out out1')

eBounds = And(0 <= e, e <= 4)   # environment actions/inputs
uBounds = And(-1 <= u, u <= 1)  # control actions/inputs
updatePred = And(buf1 == buf + e - out, out1 == out + u)
updateAction = {'name'       :"update",
                'actionPred' :updatePred,
                'envVar'     :[e],
                'envPred'    :eBounds,
                'controlVar' :[u],
                'controlPred':uBounds}

#initialState = And(0 <= buf, buf <= 20, 0 <= out, out <= 4)   #Expr
#delta1 = substitute(initialState, (buf,buf1),(out,out1))

state       = [buf, out]
state1      = [buf1,out1]
subst       = [(buf,buf1),(out,out1)]
stateInv    = And(0 <= buf, 0 <= out)
transitions = [updateAction]
initProps   = [buf == 0, out == 0]
safetyProps = [0 <= buf, buf <= 20, 0 <= out, out <= 4]
