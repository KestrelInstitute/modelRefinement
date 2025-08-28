----------------------------- MODULE TokeneerII -----------------------------
(*History TokeneerII-hist
04/20/21 - SN - created by prop refinement of UnlockPre on TokeneerI
04/27 - SN - fully incorporates the paper definitions into the TLA
*)
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
MAX_TIME, K,
WAIT, INSERT_ACTION, UNLOCK_ACTION, LOCK_ACTION, REMOVE_ACTION\*, OPEN_ACTION, CLOSE_ACTION

(*TYPES*)
Time == 0 .. (MAX_TIME+1) \* Needs +1 b/c somehow TLC increments the clock one past MAX_TIME??
Action == {INSERT_ACTION, UNLOCK_ACTION, LOCK_ACTION, REMOVE_ACTION}\*, OPEN_ACTION, CLOSE_ACTION}

VARIABLE locked     (* is the door locked? *)
VARIABLE token      (* is there a token in the reader? *)
VARIABLE open       (* is the door open? *)

\*+TII
VARIABLE lastInsertT    (* FD variable represents max{j:Time | j \in dom(hist) /\ hist(j) |= Insert}
                           last time that a card was inserted in reader *)
VARIABLE clock          (* what is the current time? *)
\*VARIABLES insertAction, removeAction, unlockAction, lockAction
VARIABLES hist, len

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
    /\  locked'=FALSE /\ (*+TII*)hist'=addToHist(UNLOCK_ACTION) /\ 
            UNCHANGED <<token, open, lastInsertT>>

(* 2. Lock the Latch *)
Lock ==
        ~locked \*this needed at this stage? /\ token
    /\  locked'=TRUE /\ hist'=addToHist(LOCK_ACTION)(*+TII*) /\ 
            UNCHANGED <<token, open, lastInsertT>>

(* --- ENV ACTIONS --- *)
(* 3. Insert the Token *)
Insert == 
        ~token
    /\  token'=TRUE /\ lastInsertT' = clock' /\ hist' = addToHist(INSERT_ACTION) (*+TII*) /\ 
            UNCHANGED <<locked, open>>
        
(* 4. Remove the Token *)
Remove == 
        token
    /\  token'=FALSE /\ hist' = addToHist(REMOVE_ACTION)(*+TII*) /\ 
            UNCHANGED <<locked, open, lastInsertT>>
    
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

Init ==
    /\ locked = TRUE
    /\ token = FALSE
    /\ open = FALSE
    /\ lastInsertT = MAX_TIME (* end of time *)  \*+TII
    /\ clock = 0
    /\ len = 0
    /\ hist = <<>>
    /\ TypeCheck

vars == <<locked, token, open, (*+TII*)  lastInsertT, clock, hist, len>>
varsXclock == <<locked, token, open, (*+TII*) lastInsertT, hist, len>>
     
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
    
Next == ClockTick (*+TII*) /\ SysOrEnvOrSkip
            
Spec == Init /\ [][Next]_vars 

(* REQUIRED PROPERTIES - Don't hold at this level *)
(* any Unlock action must be preceded by a card Insert within k time units and token is still in*)
\*UnlockPre == Unlock => (<_>_K Insert)
\*after prop transform this become
\*ORIG: UnlockPre == [][Unlock => (clock <= lastInsertT + K /\ token)]_vars 
\*The above works here, but more complex props eg with nested [], TLA doesn't like, so it becomes:
UnlockPre == (hist # <<>> /\ UNLOCK_ACTION \in last(hist)) => (clock <= lastInsertT + K (*/\ token*))

histunlockAction == [][Unlock => last(hist')=UNLOCK_ACTION]_vars
histlockAction ==   [][Lock => last(hist')=LOCK_ACTION]_vars
histinsertAction == [][Insert => last(hist')=INSERT_ACTION]_vars
histremoveAction == [][Remove => last(hist')=REMOVE_ACTION]_vars
\*not correct i believe; lastInsertT == [](lastInsertTT = max({t \in Time : t = clock /\ insertAction}))
histlastInsertT == [](lastInsertT = max({t \in 1 .. Len(hist) : INSERT_ACTION \in hist[t]}))
histInit == Len(hist)=0                         \*history is initially empty
histInc == [][Len(hist') = Len(hist)+1]_vars   \*history is incremented every step


THEOREM Spec => []TypeCheck
THEOREM Spec => []UnlockPre

=============================================================================
\* Modification History
\* Last modified Thu Apr 29 13:29:43 PDT 2021 by snedunu
\* Created Thu May 21 11:41:05 PDT 2020 by snedunu














\*curr_action ==
\*    CASE 
\*        unlockAction -> UNLOCK_ACTION
\*    []  lockAction -> LOCK_ACTION
\*    []  insertAction -> INSERT_ACTION
\*    []  removeAction -> REMOVE_ACTION
\*mutual exclusivity : foo == [](unlockAction => ~lockAction /\ ~insertAction
