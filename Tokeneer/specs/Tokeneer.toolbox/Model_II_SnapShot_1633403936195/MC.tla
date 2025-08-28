---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_16334039327119000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4MAX_TIME
const_163340393271110000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_163340393271111000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_163340393271112000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_163340393271112000>>)
----

=============================================================================
\* Modification History
\* Created Mon Oct 04 20:18:52 PDT 2021 by snedunu
