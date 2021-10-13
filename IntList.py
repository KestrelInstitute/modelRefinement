# Spec of IntLists
# python model_sched.py
from z3 import *

IntList = Datatype('IntList')
IntList.declare('nil')
IntList.declare('cons', ('car', IntSort()), ('cdr', IntList))
IntList = IntList.create()
cons = IntList.cons
car  = IntList.car
cdr  = IntList.cdr
nil  = IntList.nil
ordered = Function('ordered', IntList, BoolSort())
concat  = Function('concat', IntList, IntList, IntList)

Bag = DeclareSort('Bag')
bag       = Function('bag', IntList, Bag)
bag_nil   = Function('bag_nil', Bag)
bag_add   = Function('bag_add', IntSort(), Bag, Bag)
bag_union = Function('bag_union', Bag, Bag, Bag)
le        = Function('le', Bag, Bag, BoolSort())

# variables
#x,y,z  = Consts('x y z', IntList)
#z1,z2  = Consts('z1 z2', IntList)

# assert this, then use propagate-value: ordered(nil) == True,

#axioms = [ ordered(nil) == True,
#           ForAll([x,y], ordered(concat(x,y)) == And(ordered(x), le(bag(x),bag(y)), ordered(y))),
#           ForAll([x,y],     bag(concat(x,y)) == bag_union(bag(x), bag(y)))
#           #ordered(concat(z1, z2)) == And(ordered(z1), le(bag(z1),bag(z2)), ordered(z2)),
#           #bag(concat(z1, z2)) == bag_union(bag(z1), bag(z2))
#           ]

# moved to model_sorting.py
#IntListRewrites = [ #(ordered(nil), True),
#    (ordered(concat(z1, z2)), And(ordered(z1), le(bag(z1),bag(z2)), ordered(z2))),
#    (bag(concat(z1, z2)),  bag_union(bag(z1), bag(z2)))]
    
