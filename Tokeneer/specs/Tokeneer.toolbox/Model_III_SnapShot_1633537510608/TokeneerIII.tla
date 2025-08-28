----------------------------- MODULE TokeneerIII -----------------------------
(*History TokeneerIII-hist
04/29 - SN - recreated by prop refinement of revised TokeneerII
04/27 - SN - fully incorporates the paper definitions into the TLA
04/20/21 - SN - created by prop refinement of UnlockPre on TokeneerI
*)
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
MAX_TIME, K,
WAIT, INSERT_ACTION, UNLOCK_ACTION, LOCK_ACTION, REMOVE_ACTION\*, OPEN_ACTION, CLOSE_ACTION

(*TYPES*)
Time == 0 .. (MAX_TIME+1) \* Needs +1 b/c somehow TLC increments the clock one past MAX_TIME??
Action == {INSERT_ACTION, UNLOCK_ACTION, LOCK_ACTION, REMOVE_ACTION}\*, OPEN_ACTION, CLOSE_ACTION}

VARIABLES
locked,         (* is the door locked? *)
token,          (* is there a token in the reader? *)
open            (* is the door open? *)
,
\*+TII
lastInsertT,    (* FD variable represents max{j:Time | j \in dom(hist) /\ hist(j) |= Insert}
                           last time that a card was inserted in reader *)
clock,          (* what is the current time? *)
\*VARIABLES insertAction, removeAction, unlockAction, lockAction
hist, len
,
\*+TIII
lastUnlockT,    (* FD variable represents max{j:Time | j \in dom(hist) /\ hist(j) |= Unlock}
                               the last time an unlock action took place *)
unlockTriggerT,  (* this is actually same as lastInsertT but is gen'd by prop ref*)
insertHappened  (* persistent marker to note InsertAction happened *)

(*UTIL*)
max(S) == CHOOSE x : x \in S /\ \A y \in S: y <= x

first(xs) == SubSeq(xs,1,Len(xs)-1)

last(xs) == xs[Len(xs)]

\*if this is the first action being added for this time point, create and add new singleton entry
\*otherwise add the action to the existing entry for this time point
addToHist(action) ==    
    IF Len(hist) = len 
    THEN Print("addToHist: cond is true", Append(hist, {action})) 
    ELSE LET curr_state_acts == last(hist) IN Append(first(hist), curr_state_acts \cup {action})


(* --- SYSTEM ACTIONS --- *)
(* 1. Unlock the Latch  *)
Unlock ==
        locked /\ token /\ 
            clock' <= lastInsertT + K \*+TII implements Unlock => <.>_k Insert /\ token
    /\  locked'=FALSE /\ (*+TII*)hist'=addToHist(UNLOCK_ACTION) /\ lastUnlockT' = clock' /\
            UNCHANGED <<token, open, lastInsertT, unlockTriggerT, insertHappened>>

(* 2. Lock the Latch *)
Lock ==
        ~locked \*this needed at this stage? /\ token
    /\  locked'=TRUE /\ (*+TII*) hist'=addToHist(LOCK_ACTION) /\ 
            UNCHANGED <<token, open, lastInsertT, lastUnlockT, unlockTriggerT, insertHappened>>

(* --- ENV ACTIONS --- *)
(* 3. Insert the Token *)
Insert == 
        ~token
    /\  token'=TRUE /\ (*+TII*) lastInsertT' = clock' /\ hist' = addToHist(INSERT_ACTION) /\ insertHappened'=TRUE /\
            (*+TIII*) unlockTriggerT' = clock' /\ 
            UNCHANGED <<locked, open, lastUnlockT>>
        
(* 4. Remove the Token *)
Remove == 
        token
    /\  token'=FALSE /\ hist' = addToHist(REMOVE_ACTION)(*+TII*) /\ 
            UNCHANGED <<locked, open, lastInsertT, lastUnlockT, unlockTriggerT, insertHappened>>
    
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
     \*+TII
     /\ clock \in Nat   
     /\ lastInsertT \in Time
     /\ hist \in Seq(SUBSET Action)
     (*+TIII*)
     /\ lastUnlockT \in Time
     /\ unlockTriggerT \in Time
     /\ insertHappened \in BOOLEAN

Init ==
    /\ locked = TRUE
    /\ token = FALSE
    /\ open = FALSE
    \*+TII
    /\ lastInsertT = MAX_TIME (* end of time *)  
    /\ clock = 0
    /\ len = 0
    /\ hist = <<>>
    (*+TIII*)
    /\ lastUnlockT = MAX_TIME
    /\ unlockTriggerT = MAX_TIME
    /\ insertHappened = FALSE
    /\ TypeCheck

vars == <<locked, token, open, (*+TII*) lastInsertT, clock, hist, len, 
        (*+TIII*)lastUnlockT, unlockTriggerT, insertHappened>>
varsXclock == <<locked, token, open, (*+TII*) lastInsertT, hist, len, lastUnlockT, unlockTriggerT, insertHappened>>
\*vars_subset == <<locked, token, open, lastInsertT, lastUnlockT, unlockTriggerT>>

EnvActs == 
    \/  Insert
    \/  Remove
\*    \/  Open
\*    \/  Close

SysActs == 
        Unlock
    \/  Lock

DoNothing == UNCHANGED varsXclock /\ hist'=addToHist(WAIT)

SysOrEnvOrSkip == (EnvActs \/ SysActs \/ DoNothing) /\ (*+TII*) len' = Len(hist')

ClockTick == clock' = clock+1                   \*Now a constraint in the model: clock <= MAX_TIME

(* OLD not correct, and TLC also won't accept
TBound(A, start, minT, maxT) ==    (* prevents time from progressing after max unless A happens *)
    \*ENABLED is here so the time constraint only applies when its needed, ie A still needs to happn
    LET atMostMax == ENABLED(A) => (clock <= start + maxT)
        atLeastMin == A => (clock >= start + minT) 
    IN  atLeastMin /\ atMostMax
*)
(*
SS book has a def of RTBound that is a modification of the WF requirement for real-time but still
requires that A be continually enabled, (which *may* be a bit stronger then we need). 
RTBound(A,vs,minT,maxT) ==
    LET TNext(t) == t' = IF <A>_v \/ ~(ENABLED <A>_v)' \*A happens or it becomes disabled
                         THEN 0
                         ELSE t + (clock'-clock)
        Timer(t) == t== 0 /\ [][TNext(t)]_<<t,clock,vs>>
        atMostMax(t) == [](t <= max)
        atLeastMin(t) == [][A => min <= min]_vs
    IN  \EE t: Timer(t) /\ atLeastMin(t) /\ atMostMax(t)
*)
(* ACTION CONSTRAINT +TIII *)
TBound(lastAT, start, minT, maxT) ==
    LET atMostMax == lastAT < start => clock <= start + maxT
        atLeastMin == TRUE \*not needed: A => (clock >= start + minT) 
    IN  atLeastMin /\ atMostMax
    
\*old CheckTimeConstraint == TBound(Unlock, lastInsertT, 1, K-1) \* <-- should be unlockTriggerT ?
CheckTimeConstraint == TBound(lastUnlockT, unlockTriggerT, 1, K-1) 

\*Next == (*+TII*)ClockTick /\ SysOrEnvOrSkip 
\*Spec == Init /\ [][Next]_vars /\ RTBound(Unlock, vars, 1, K-1)

Next == (*+TII*)ClockTick /\ SysOrEnvOrSkip /\ (*+TIII:*)CheckTimeConstraint 
Spec == Init /\ [][Next]_vars 

(* REQUIRED PROPERTIES - Don't hold at this level *)
(* any Unlock action must be preceded by a card Insert within k time units and token is still in*)
\*UnlockPre == Unlock => (<_>_K Insert)
\*after prop transform this become
\*ORIG: 
UnlockPre == [][Unlock => (clock <= lastInsertT + K /\ token)]_vars 
\*The above works here, but more complex props eg with nested [], TLA doesn't like, so it becomes:
\*UnlockPre == (hist # <<>> /\ UNLOCK_ACTION \in last(hist)) => (clock <= lastInsertT + K (*/\ token*))

histunlockAction == [][Unlock => last(hist')=UNLOCK_ACTION]_vars
histlockAction ==   [][Lock => last(hist')=LOCK_ACTION]_vars
histinsertAction == [][Insert => last(hist')=INSERT_ACTION]_vars
histremoveAction == [][Remove => last(hist')=REMOVE_ACTION]_vars
\*not correct i believe; lastInsertT == [](lastInsertTT = max({t \in Time : t = clock /\ insertAction}))
histlastInsertT == [](lastInsertT = max({t \in 1 .. Len(hist) : INSERT_ACTION \in hist[t]}))
histInit == Len(hist)=0                         \*history is initially empty
histInc == [][Len(hist') = Len(hist)+1]_vars   \*history is incremented every step

(*+TIII*)
(*lastUnlockT == max{j:Time | j \in dom(hist) /\ hist(j) |= Insert} <-- this is eliminated by FD
    Insert => (<>_K Unlock)
after prop transform and FD this become
    [][Insert => (unlockTriggerT = clock /\ 
                        [] (lastUnlockT < unlockTriggerT  =>  clock <= unlockTriggerT + K))]_vars
but TLA doesn't like nested [] for step formulas, so use hist and transform to:
TLA doesn't like nested [] invariants either.. 
InsertLeadsToUnlocked == 
    (hist # <<>> /\ INSERT_ACTION \in last(hist)) => 
        (unlockTriggerT = clock /\ 
         [] (lastUnlockT < unlockTriggerT  =>  clock <= unlockTriggerT + K))
\*    insertActionGood == [][(Insert => insertAction'=TRUE) /\ (insertAction'=TRUE => Insert)]_vars
*)
\*when does InsertHappened get turned off??
InsertLeadsToUnlocked ==
    insertHappened => (lastUnlockT < unlockTriggerT  =>  clock <= unlockTriggerT + K)
InsertHappenedPersists == 
    [][Insert => unlockTriggerT' = clock /\ insertHappened'=TRUE]_vars
InsertHappenedSet ==
    [][insertHappened => insertHappened' = TRUE]_vars

THEOREM Spec => []TypeCheck
THEOREM Spec => []UnlockPre
THEOREM Spec => []InsertLeadsToUnlocked
=============================================================================
\* Modification History
\* Last modified Wed Oct 06 09:25:01 PDT 2021 by snedunu
\* Created Thu May 21 11:41:05 PDT 2020 by snedunu














\*curr_action ==
\*    CASE 
\*        unlockAction -> UNLOCK_ACTION
\*    []  lockAction -> LOCK_ACTION
\*    []  insertAction -> INSERT_ACTION
\*    []  removeAction -> REMOVE_ACTION
\*mutual exclusivity : foo == [](unlockAction => ~lockAction /\ ~insertAction
