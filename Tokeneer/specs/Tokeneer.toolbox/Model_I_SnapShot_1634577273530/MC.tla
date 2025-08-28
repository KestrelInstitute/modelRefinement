---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1634577271492351000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1634577271492352000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1634577271492353000 ==
clock <= MAX_TIME
----
=============================================================================
\* Modification History
\* Created Mon Oct 18 10:14:31 PDT 2021 by snedunu
