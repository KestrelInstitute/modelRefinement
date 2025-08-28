---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_16348551990418000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_16348551990419000 == 
7
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_163485519904110000 ==
clock <= MAX_TIME
----
=============================================================================
\* Modification History
\* Created Thu Oct 21 15:26:39 PDT 2021 by snedunu
