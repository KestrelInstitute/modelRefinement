----------------------------- MODULE TokeneerIII -----------------------------
(*History TokeneerIII-hist
10/04 - SN - completely revamped as per the new property transform approach in paper
04/29 - SN - recreated by prop refinement of revised TokeneerII
04/27 - SN - fully incorporates the paper definitions into the TLA
04/20/21 - SN - created by prop refinement of UnlockPre on TokeneerI
*)
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
MAX_TIME, K

(*TYPES*)
Time == 0 .. (MAX_TIME+1) \* Needs +1 b/c somehow TLC increments the clock one past MAX_TIME??

VARIABLES
locked,         (* is the door locked? *)
token,          (* is there a token in the reader? *)
open            (* is the door open? *)
,
lastInsertT,    (* FD variable represents max{j:Time | j \in dom(hist) /\ hist(j) |= Insert}
                           last time that a card was inserted in reader *)
clock,          (* what is the current time? *)
lastUnlockT,    (* FD variable represents max{j:Time | j \in dom(hist) /\ hist(j) |= Unlock}
                               the last time an unlock action took place *)
unlockTriggerT  (* this is actually same as lastInsertT but is gen'd by prop ref*)

(* --- SYSTEM ACTIONS --- *)
(* 1. Unlock the Latch  *)
Unlock ==
        locked /\ token (*w/o this, it deadlocks*) /\ 
            clock <= lastInsertT + K 
    /\  locked'=FALSE /\ lastUnlockT' = clock /\
            UNCHANGED <<token, open, lastInsertT, unlockTriggerT>>

(* 2. Lock the Latch *)
Lock ==
        ~locked \*this needed at this stage? /\ token
    /\  locked'=TRUE /\ UNCHANGED <<token, open, lastInsertT, lastUnlockT, unlockTriggerT>>

(* --- ENV ACTIONS --- *)
(* 3. Insert the Token *)
Insert == 
        ~token /\ (*to prevent a *) locked /\
    /\  token'=TRUE /\ lastInsertT' = clock /\ unlockTriggerT' = clock /\ 
        UNCHANGED <<locked, open, lastUnlockT>>
        
(* 4. Remove the Token *)
Remove == 
        token
    /\  token'=FALSE /\ UNCHANGED <<locked, open, lastInsertT, lastUnlockT, unlockTriggerT>>
    
(* Temporarily removed to reduce problem to its essence
(* 5. Open the Door *)
Open == 
        ~open /\ ~locked
    /\  open'=TRUE /\ UNCHANGED <<locked, token, lastInsertT>>
    
Open1 == Open /\ hist' = Append(hist, OPEN_ACTION)

(* 6. Close the Door *)
Close ==
        open
    /\  open'=FALSE /\ UNCHANGED <<locked, token, lastInsertT>>
    
Close1 == Close /\ hist' = Append(hist, CLOSE_ACTION)
*)

(* --------- the specification of behavior  ----------------- *)
TypeCheck ==      
     /\ locked \in BOOLEAN 
     /\ token  \in BOOLEAN 
     /\ open   \in BOOLEAN
     /\ clock \in Nat   
     /\ lastInsertT \in Time
     /\ lastUnlockT \in Time
     /\ unlockTriggerT \in Time

Init ==
    /\ locked = TRUE
    /\ token = FALSE
    /\ open = FALSE
    /\ clock = 0
    /\ lastInsertT = MAX_TIME (* end of time *)  
    /\ lastUnlockT = MAX_TIME
    /\ unlockTriggerT = MAX_TIME
    /\ TypeCheck

vars == <<locked, token, open, lastInsertT, clock, lastUnlockT, unlockTriggerT>>
varsXclock == <<locked, token, open, lastInsertT, lastUnlockT, unlockTriggerT>>

EnvActs == 
    \/  Insert
    \/  Remove

SysActs == 
        Unlock
    \/  Lock

DoNothing == UNCHANGED varsXclock 

SysOrEnvOrSkip == (EnvActs \/ SysActs \/ DoNothing) 

ClockTick == clock' = clock+1                   \*Now a constraint in the model: clock <= MAX_TIME

TBound(lastAT, start, minT, maxT) ==
    LET atMostMax == lastAT < start => clock <= start + maxT
\*    LET atMostMax == lastAT < start => clock' <= start + maxT
        atLeastMin == TRUE \*not needed: A => (clock >= start + minT) 
    IN  atLeastMin /\ atMostMax
    
\*old CheckTimeConstraint == TBound(Unlock, lastInsertT, 1, K-1) \* <-- should be unlockTriggerT ?
\*CheckTimeConstraint == TBound(lastUnlockT, unlockTriggerT, 1, K-1) 
CheckTimeConstraint == TBound(lastUnlockT', unlockTriggerT, 1, K) 

Next == ClockTick /\ SysOrEnvOrSkip /\ CheckTimeConstraint
Spec == Init /\ [][Next]_vars 


(* Insert leads to unlock within k timesteps
[](Insert => <>_K Unlock)
which property transforms (see paper) turn it into*)
InsertLeadsToUnlocked == unlockTriggerT > lastUnlockT => clock <= unlockTriggerT + K
(*and requires*)
UnlockTSetProp == [][Unlock => lastUnlockT' = clock]_vars
UnlockTriggerTSetProp == [][Insert => unlockTriggerT' = clock]_vars

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

THEOREM Spec => []TypeCheck
\*THEOREM Spec => UnlockPre
THEOREM Spec => []InsertLeadsToUnlocked
=============================================================================
\* Modification History
\* Last modified Thu Oct 07 09:44:21 PDT 2021 by snedunu
\* Created Thu May 21 11:41:05 PDT 2020 by snedunu














\*curr_action ==
\*    CASE 
\*        unlockAction -> UNLOCK_ACTION
\*    []  lockAction -> LOCK_ACTION
\*    []  insertAction -> INSERT_ACTION
\*    []  removeAction -> REMOVE_ACTION
\*mutual exclusivity : foo == [](unlockAction => ~lockAction /\ ~insertAction
