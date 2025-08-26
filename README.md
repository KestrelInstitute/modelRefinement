
Model refinement tool. v1 handles only one node. v2 handles multinode.

Does everything V2 does plus:
- refactored
- correctly handles step predicates that require the node invariant to establish
- permits both "\A e. E(). \E u. U()" and "\E u. U(). \A e. E()" forms
- reinstates explicit refinement of guard condition
