---- MODULE MC ----
EXTENDS TokeneerDS, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1601066955542112000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1601066955542113000 == 
6
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1601066955542114000 ==
clock <= MAX_TIME
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1601066955542115000 ==
[]UnlockPre
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1601066955542116000 ==
[]InsertLeadsToUnlocked
----
=============================================================================
\* Modification History
\* Created Fri Sep 25 13:49:15 PDT 2020 by snedunu
