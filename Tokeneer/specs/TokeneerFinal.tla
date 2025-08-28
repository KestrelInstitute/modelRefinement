----------------------------- MODULE TokeneerFinal -----------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC 

CONSTANTS 
MAX_TIME, K

(*TYPES*)
Time == -MAX_TIME .. (MAX_TIME+1) \* Needs +1 b/c somehow TLC increments the clock one past MAX_TIME??

VARIABLES
clock,              (* what is the current time? *)
locked,             (* is the door locked? *)
token,              (* is there a token in the reader? *)
lastInsertT,        (* last time that a card was inserted in reader *)
unlockDeadlines,    (* set of deadlines for when to unlock *)
lastUnlockT         (* need to express the Eventually property below *)

vars == <<clock, locked, token, lastInsertT, unlockDeadlines, lastUnlockT>>
varsXclock == << locked, token, lastInsertT, unlockDeadlines, lastUnlockT>>

TypeCheck ==      
     /\ locked \in BOOLEAN 
     /\ token  \in BOOLEAN 
     /\ clock \in Nat
     /\ lastInsertT \in Time
     /\ lastUnlockT \in Time
     /\ \A x \in unlockDeadlines: x \in Nat  \*everything in TLA is a set

\*                       MAX_TIME+1 so CheckTimeConstraint' below doesn't block when clock reaches MAX_TIME
min(xs) == IF xs={} THEN MAX_TIME+1 ELSE CHOOSE x \in xs : (\A y \in xs: x <= y)

(* --- SYSTEM ACTIONS --- *)
(* 1. Unlock the Latch  *)
Unlock ==
        clock <= lastInsertT + K
    /\  locked'=FALSE /\ unlockDeadlines' = {} /\ lastUnlockT' = clock /\ 
            UNCHANGED <<token, lastInsertT>>

(* 2. Lock the Latch *)
Lock ==
    locked'=TRUE /\ UNCHANGED <<token, lastInsertT, unlockDeadlines, lastUnlockT>>

(* --- ENV ACTIONS --- *)
(* 3. Insert the Token *)
Insert == 
        ~token
    /\  token'=TRUE /\ 
        lastInsertT'=clock /\ unlockDeadlines' = unlockDeadlines \union {clock+K} /\ 
        UNCHANGED <<locked, lastUnlockT>>
        
(* 4. Remove the Token *)
Remove == 
        token
    /\  token'=FALSE /\ UNCHANGED <<locked, lastInsertT, unlockDeadlines, lastUnlockT>>
    
(* --------- the specification of behavior  ----------------- *)
Init ==
    /\ locked = TRUE
    /\ token = FALSE
    /\ clock = 0
    /\ lastInsertT = -MAX_TIME (* end of time *)
    /\ lastUnlockT = MAX_TIME  
    /\ unlockDeadlines = {}
    /\ TypeCheck

EnvActs == 
    \/  Insert
    \/  Remove

SysActs == 
    \/  Unlock
    \/  Lock

DoNothing == UNCHANGED varsXclock 

(* state invariant *)
CheckTimeConstraint == clock <= min(unlockDeadlines)

(*CheckTimeConstraint' performs a "lookahead" to ensure we don't transition to a state that doesn't
  satisfy the invariant*)
SysOrEnvOrSkip == (EnvActs \/ SysActs \/ DoNothing) /\ CheckTimeConstraint'

ClockTick == clock' = clock+1                   \*Now a constraint in the model: clock <= MAX_TIME

Next == ClockTick /\ SysOrEnvOrSkip (*SN: added*) /\ CheckTimeConstraint
Spec == Init /\ [][Next]_vars 

(* any Unlock action must be preceded by a card Insert within k time units
UnlockPre == Unlock => (<_>_K Insert)
after prop transform this become
*)
InsertBeforeUnlock== [][Unlock => (clock <= lastInsertT + K)]_vars 

(* Insert leads to unlock within k timesteps
    [](Insert => <>_K Unlock)
which property transforms (see paper) turn it into
    InsertLeadsToUnlocked == [][Insert => unlockDeadlines' = unlockDeadlines \union {clock+K}]_vars
but this is already incorporated into the spec
*)
UnlockHappened == lastUnlockT \in lastInsertT .. clock
InsertLeadsToUnlocked == 
    [][(lastInsertT # -MAX_TIME /\ lastInsertT < clock /\ ~UnlockHappened) =>
        clock <= min(unlockDeadlines)]_vars

THEOREM Spec => []TypeCheck
THEOREM Spec => InsertBeforeUnlock
THEOREM Spec => InsertLeadsToUnlocked
=============================================================================
\* Modification History
\* Last modified Fri Oct 22 09:35:36 PDT 2021 by snedunu
\* Created Thu May 21 11:41:05 PDT 2020 by snedunu


















(*Note this was originally after prop transforms and FD expressed as
    [][Insert => (unlockTriggerT = clock /\ 
                        [] (lastUnlockT < unlockTriggerT  =>  clock <= unlockTriggerT + K))]_vars
but TLA doesn't like nested [] for step formulas, or for that matter in invariants either.. 
InsertLeadsToUnlocked == 
    (hist # <<>> /\ INSERT_ACTION \in last(hist)) => 
        (unlockTriggerT = clock /\ 
         [] (lastUnlockT < unlockTriggerT  =>  clock <= unlockTriggerT + K))
This required maintaining an action history, see TokeneerIII_w_history
*)
\*TBound(lastAT, start, minT, maxT) ==
\*    LET atMostMax == lastAT < start => clock <= start + maxT
\*\*    LET atMostMax == lastAT < start => clock' <= start + maxT
\*        atLeastMin == TRUE \*not needed: A => (clock >= start + minT) 
\*    IN  atLeastMin /\ atMostMax
    
\*old CheckTimeConstraint == TBound(Unlock, lastInsertT, 1, K-1) \* <-- should be unlockTriggerT ?
\*CheckTimeConstraint == TBound(lastUnlockT, unlockTriggerT, 1, K-1) 
\*CheckTimeConstraint == TBound(lastUnlockT, unlockTriggerT, 1, K) 

