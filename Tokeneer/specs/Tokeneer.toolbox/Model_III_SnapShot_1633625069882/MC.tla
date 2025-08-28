---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1634431745863237000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1634431745863238000 == 
9
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1634431745863239000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1634431745863240000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1634431745863240000>>)
----

=============================================================================
\* Modification History
\* Created Sat Oct 16 17:49:05 PDT 2021 by snedunu
