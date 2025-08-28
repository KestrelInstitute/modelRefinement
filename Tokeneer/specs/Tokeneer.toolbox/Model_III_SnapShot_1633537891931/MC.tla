---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1633537888897235000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1633537888897236000 == 
9
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633537888897237000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1633537888897238000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1633537888897238000>>)
----

=============================================================================
\* Modification History
\* Created Wed Oct 06 09:31:28 PDT 2021 by snedunu
