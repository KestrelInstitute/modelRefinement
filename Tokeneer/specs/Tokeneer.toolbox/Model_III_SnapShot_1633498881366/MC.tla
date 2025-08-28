---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1633498878328169000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1633498878328170000 == 
8
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633498878328171000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1633498878328172000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1633498878328172000>>)
----

=============================================================================
\* Modification History
\* Created Tue Oct 05 22:41:18 PDT 2021 by snedunu
