---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_16348550983662000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_16348550983673000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_16348550983674000 ==
clock <= MAX_TIME
----
=============================================================================
\* Modification History
\* Created Thu Oct 21 15:24:58 PDT 2021 by snedunu
