---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1633537703596217000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1633537703596218000 == 
8
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633537703596219000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1633537703596220000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1633537703596220000>>)
----

=============================================================================
\* Modification History
\* Created Wed Oct 06 09:28:23 PDT 2021 by snedunu
