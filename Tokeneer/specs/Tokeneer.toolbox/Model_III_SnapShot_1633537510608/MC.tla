---- MODULE MC ----
EXTENDS Tokeneer, TLC

\* CONSTANT definitions @modelParameterConstants:0K
const_1633537507563205000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1633537507563206000 == 
8
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633537507563207000 ==
clock <= MAX_TIME
----
\* Constant expression definition @modelExpressionEval
const_expr_1633537507563208000 == 
{"A"} \cup {"B"}
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1633537507563208000>>)
----

=============================================================================
\* Modification History
\* Created Wed Oct 06 09:25:07 PDT 2021 by snedunu
