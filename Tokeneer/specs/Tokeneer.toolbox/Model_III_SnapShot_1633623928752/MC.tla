---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1633623925722254000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1633623925722255000 == 
9
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633623925722256000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1633623925722257000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1633623925722257000>>)
----

=============================================================================
\* Modification History
\* Created Thu Oct 07 09:25:25 PDT 2021 by snedunu
