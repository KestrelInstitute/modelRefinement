---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1633623886716241000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1633623886716242000 == 
9
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633623886716243000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1633623886716244000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1633623886716244000>>)
----

=============================================================================
\* Modification History
\* Created Thu Oct 07 09:24:46 PDT 2021 by snedunu
