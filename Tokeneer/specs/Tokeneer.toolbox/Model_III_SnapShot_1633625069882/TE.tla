\* :1:__trace_var_1634431825503259000:CheckTimeConstraint"$!@$!@$!@$!@$!"
\* :1:__trace_var_1634431825503261000:ENABLED(Lock)"$!@$!@$!@$!@$!"
\* :2:__trace_var_1634431825503263000:CheckTimeConstraint'"$!@$!@$!@$!@$!"
---- MODULE TE ----
EXTENDS Tokeneer, Toolbox, TLC, Naturals

\* CONSTANT definitions @modelParameterConstants:0K
const_1634431825520267000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1MAX_TIME
const_1634431825520268000 == 
9
----

def_ov_1634431825520269000 == 
    <<
    ([lastInsertT |-> -9,unlockDeadlines |-> {},clock |-> 0,token |-> FALSE,insertHappened |-> FALSE,lastUnlockT |-> 9,locked |-> TRUE]),
    ([lastInsertT |-> 0,unlockDeadlines |-> {3},clock |-> 1,token |-> TRUE,insertHappened |-> TRUE,lastUnlockT |-> 9,locked |-> TRUE]),
    ([lastInsertT |-> 0,unlockDeadlines |-> {},clock |-> 2,token |-> TRUE,insertHappened |-> TRUE,lastUnlockT |-> 1,locked |-> FALSE]),
    ([lastInsertT |-> 0,unlockDeadlines |-> {},clock |-> 3,token |-> FALSE,insertHappened |-> TRUE,lastUnlockT |-> 1,locked |-> FALSE]),
    ([lastInsertT |-> 0,unlockDeadlines |-> {},clock |-> 4,token |-> FALSE,insertHappened |-> TRUE,lastUnlockT |-> 1,locked |-> TRUE]),
    ([lastInsertT |-> 4,unlockDeadlines |-> {7},clock |-> 5,token |-> TRUE,insertHappened |-> TRUE,lastUnlockT |-> 1,locked |-> TRUE]),
    ([lastInsertT |-> 4,unlockDeadlines |-> {7},clock |-> 6,token |-> FALSE,insertHappened |-> TRUE,lastUnlockT |-> 1,locked |-> TRUE]),
    ([lastInsertT |-> 6,unlockDeadlines |-> {7, 9},clock |-> 7,token |-> TRUE,insertHappened |-> TRUE,lastUnlockT |-> 1,locked |-> TRUE]),
    ([lastInsertT |-> 6,unlockDeadlines |-> {},clock |-> 8,token |-> TRUE,insertHappened |-> TRUE,lastUnlockT |-> 7,locked |-> FALSE]),
    ([lastInsertT |-> 6,unlockDeadlines |-> {},clock |-> 9,token |-> FALSE,insertHappened |-> TRUE,lastUnlockT |-> 7,locked |-> FALSE])
    >>
----


\* TRACE EXPLORER variable declaration @traceExploreExpressions
VARIABLES __trace_var_1634431825503259000,__trace_var_1634431825503261000,__trace_var_1634431825503263000
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions:0
trace_def_1634431825503258000 ==
CheckTimeConstraint
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions:1
trace_def_1634431825503260000 ==
ENABLED(Lock)
----

\* TRACE EXPLORER identifier definition @traceExploreExpressions:2
trace_def_1634431825503262000 ==
CheckTimeConstraint'
----

\* TRACE Sub-Action definition 0
next_sa_0 ==
    (
        /\ lastInsertT = (
                -9
            )
        /\ unlockDeadlines = (
                {}
            )
        /\ clock = (
                0
            )
        /\ token = (
                FALSE
            )
        /\ insertHappened = (
                FALSE
            )
        /\ lastUnlockT = (
                9
            )
        /\ locked = (
                TRUE
            )
        /\ lastInsertT' = (
                0
            )
        /\ unlockDeadlines' = (
                {3}
            )
        /\ clock' = (
                1
            )
        /\ token' = (
                TRUE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                9
            )
        /\ locked' = (
                TRUE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Sub-Action definition 1
next_sa_1 ==
    (
        /\ lastInsertT = (
                0
            )
        /\ unlockDeadlines = (
                {3}
            )
        /\ clock = (
                1
            )
        /\ token = (
                TRUE
            )
        /\ insertHappened = (
                TRUE
            )
        /\ lastUnlockT = (
                9
            )
        /\ locked = (
                TRUE
            )
        /\ lastInsertT' = (
                0
            )
        /\ unlockDeadlines' = (
                {}
            )
        /\ clock' = (
                2
            )
        /\ token' = (
                TRUE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                1
            )
        /\ locked' = (
                FALSE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Sub-Action definition 2
next_sa_2 ==
    (
        /\ lastInsertT = (
                0
            )
        /\ unlockDeadlines = (
                {}
            )
        /\ clock = (
                2
            )
        /\ token = (
                TRUE
            )
        /\ insertHappened = (
                TRUE
            )
        /\ lastUnlockT = (
                1
            )
        /\ locked = (
                FALSE
            )
        /\ lastInsertT' = (
                0
            )
        /\ unlockDeadlines' = (
                {}
            )
        /\ clock' = (
                3
            )
        /\ token' = (
                FALSE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                1
            )
        /\ locked' = (
                FALSE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Sub-Action definition 3
next_sa_3 ==
    (
        /\ lastInsertT = (
                0
            )
        /\ unlockDeadlines = (
                {}
            )
        /\ clock = (
                3
            )
        /\ token = (
                FALSE
            )
        /\ insertHappened = (
                TRUE
            )
        /\ lastUnlockT = (
                1
            )
        /\ locked = (
                FALSE
            )
        /\ lastInsertT' = (
                0
            )
        /\ unlockDeadlines' = (
                {}
            )
        /\ clock' = (
                4
            )
        /\ token' = (
                FALSE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                1
            )
        /\ locked' = (
                TRUE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Sub-Action definition 4
next_sa_4 ==
    (
        /\ lastInsertT = (
                0
            )
        /\ unlockDeadlines = (
                {}
            )
        /\ clock = (
                4
            )
        /\ token = (
                FALSE
            )
        /\ insertHappened = (
                TRUE
            )
        /\ lastUnlockT = (
                1
            )
        /\ locked = (
                TRUE
            )
        /\ lastInsertT' = (
                4
            )
        /\ unlockDeadlines' = (
                {7}
            )
        /\ clock' = (
                5
            )
        /\ token' = (
                TRUE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                1
            )
        /\ locked' = (
                TRUE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Sub-Action definition 5
next_sa_5 ==
    (
        /\ lastInsertT = (
                4
            )
        /\ unlockDeadlines = (
                {7}
            )
        /\ clock = (
                5
            )
        /\ token = (
                TRUE
            )
        /\ insertHappened = (
                TRUE
            )
        /\ lastUnlockT = (
                1
            )
        /\ locked = (
                TRUE
            )
        /\ lastInsertT' = (
                4
            )
        /\ unlockDeadlines' = (
                {7}
            )
        /\ clock' = (
                6
            )
        /\ token' = (
                FALSE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                1
            )
        /\ locked' = (
                TRUE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Sub-Action definition 6
next_sa_6 ==
    (
        /\ lastInsertT = (
                4
            )
        /\ unlockDeadlines = (
                {7}
            )
        /\ clock = (
                6
            )
        /\ token = (
                FALSE
            )
        /\ insertHappened = (
                TRUE
            )
        /\ lastUnlockT = (
                1
            )
        /\ locked = (
                TRUE
            )
        /\ lastInsertT' = (
                6
            )
        /\ unlockDeadlines' = (
                {7, 9}
            )
        /\ clock' = (
                7
            )
        /\ token' = (
                TRUE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                1
            )
        /\ locked' = (
                TRUE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Sub-Action definition 7
next_sa_7 ==
    (
        /\ lastInsertT = (
                6
            )
        /\ unlockDeadlines = (
                {7, 9}
            )
        /\ clock = (
                7
            )
        /\ token = (
                TRUE
            )
        /\ insertHappened = (
                TRUE
            )
        /\ lastUnlockT = (
                1
            )
        /\ locked = (
                TRUE
            )
        /\ lastInsertT' = (
                6
            )
        /\ unlockDeadlines' = (
                {}
            )
        /\ clock' = (
                8
            )
        /\ token' = (
                TRUE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                7
            )
        /\ locked' = (
                FALSE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Sub-Action definition 8
next_sa_8 ==
    (
        /\ lastInsertT = (
                6
            )
        /\ unlockDeadlines = (
                {}
            )
        /\ clock = (
                8
            )
        /\ token = (
                TRUE
            )
        /\ insertHappened = (
                TRUE
            )
        /\ lastUnlockT = (
                7
            )
        /\ locked = (
                FALSE
            )
        /\ lastInsertT' = (
                6
            )
        /\ unlockDeadlines' = (
                {}
            )
        /\ clock' = (
                9
            )
        /\ token' = (
                FALSE
            )
        /\ insertHappened' = (
                TRUE
            )
        /\ lastUnlockT' = (
                7
            )
        /\ locked' = (
                FALSE
            )
        /\ __trace_var_1634431825503259000' = (
            trace_def_1634431825503258000
            )'
        /\ __trace_var_1634431825503261000' = (
            trace_def_1634431825503260000
            )'
        /\ __trace_var_1634431825503263000' = (
            trace_def_1634431825503262000
            )
    )

\* TRACE Action Constraint definition traceExploreActionConstraint
action_constr_1634431825503266000 ==
<<
next_sa_0,
next_sa_1,
next_sa_2,
next_sa_3,
next_sa_4,
next_sa_5,
next_sa_6,
next_sa_7,
next_sa_8
>>[TLCGet("level")]
----

\* TRACE INIT definition traceExploreInit
init_1634431825503264000 ==
    /\ lastInsertT = (
            -9
        )
    /\ unlockDeadlines = (
            {}
        )
    /\ clock = (
            0
        )
    /\ token = (
            FALSE
        )
    /\ insertHappened = (
            FALSE
        )
    /\ lastUnlockT = (
            9
        )
    /\ locked = (
            TRUE
        )
    /\ __trace_var_1634431825503259000 = (
            trace_def_1634431825503258000
        )
    /\ __trace_var_1634431825503261000 = (
            trace_def_1634431825503260000
        )
    /\ __trace_var_1634431825503263000 = (
            "--"
        )

----

\* TRACE NEXT definition traceExploreNext
next_1634431825503265000 ==
    \/ next_sa_0
    \/ next_sa_1
    \/ next_sa_2
    \/ next_sa_3
    \/ next_sa_4
    \/ next_sa_5
    \/ next_sa_6
    \/ next_sa_7
    \/ next_sa_8



_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        lastInsertT = (6)
        /\
        unlockDeadlines = ({})
        /\
        clock = (9)
        /\
        token = (FALSE)
        /\
        insertHappened = (TRUE)
        /\
        lastUnlockT = (7)
        /\
        locked = (FALSE)
    )
----

=============================================================================
\* Modification History
\* Created Sat Oct 16 17:50:25 PDT 2021 by snedunu
