---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1634582675322364000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1634582675330365000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1634582675330366000 ==
clock <= MAX_TIME
----
=============================================================================
\* Modification History
\* Created Mon Oct 18 11:44:35 PDT 2021 by snedunu
