---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_163492046885126000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_163492046885127000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_163492046885128000 ==
clock <= MAX_TIME
----
=============================================================================
\* Modification History
\* Created Fri Oct 22 09:34:28 PDT 2021 by snedunu
