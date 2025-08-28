---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_163340416683716000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4MAX_TIME
const_163340416683717000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_163340416683718000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_163340416683719000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_163340416683719000>>)
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_163340416683821000 ==
LastInsertTProp
----
=============================================================================
\* Modification History
\* Created Mon Oct 04 20:22:46 PDT 2021 by snedunu
