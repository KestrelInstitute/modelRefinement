---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1633625066843287000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1633625066843288000 == 
9
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633625066843289000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1633625066843290000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1633625066843290000>>)
----

=============================================================================
\* Modification History
\* Created Thu Oct 07 09:44:26 PDT 2021 by snedunu
