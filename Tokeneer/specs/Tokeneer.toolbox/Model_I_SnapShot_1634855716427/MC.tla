---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_163485571236120000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_163485571236121000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_163485571236122000 ==
clock <= MAX_TIME
----
=============================================================================
\* Modification History
\* Created Thu Oct 21 15:35:12 PDT 2021 by snedunu
