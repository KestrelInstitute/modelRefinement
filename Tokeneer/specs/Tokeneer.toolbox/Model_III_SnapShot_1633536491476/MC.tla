---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1633536488101199000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1633536488101200000 == 
8
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633536488101201000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1633536488101202000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1633536488101202000>>)
----

=============================================================================
\* Modification History
\* Created Wed Oct 06 09:08:08 PDT 2021 by snedunu
