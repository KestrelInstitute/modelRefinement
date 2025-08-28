---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1634577479539355000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1634577479539356000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1634577479540357000 ==
clock <= MAX_TIME
----
=============================================================================
\* Modification History
\* Created Mon Oct 18 10:17:59 PDT 2021 by snedunu
