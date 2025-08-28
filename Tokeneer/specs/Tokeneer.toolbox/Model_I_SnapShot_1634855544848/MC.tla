---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_163485554078814000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_163485554078815000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_163485554078816000 ==
clock <= MAX_TIME
----
=============================================================================
\* Modification History
\* Created Thu Oct 21 15:32:20 PDT 2021 by snedunu
