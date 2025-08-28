----------------------------- MODULE TokeneerDS -----------------------------
(*History
9/23/20 - SN:
    - added precond to Open of ~locked
    - changed def of InsertBeforeUnlocked to it doesn't permit intervening Lock action
    - lastInsert' = clock --> lastInsert' = clock'. Changed arg to call of RTBound to K-1
    - reverted back to original def of RTBound. However it now deadlocks b/c there is a valid trace
      you allowed in which there its a valid prefix but there are no satisfying traces forward
      0    1    2    3  (let K=2 ie K-1=)
      |-I->|-R->| <> || deadlocked b/c both env & sys did nothin during 3rd step but RTBound is now F.
6/12/20 - SN:
-   Added the precondition locked to the Unlock action
-   TLA won't allow actions in the props so its proxied by a variable “insertAction” which is 
    set TRUE by the insert action, and false by every other action (including the “do nothing” step)
-   At this point, the spec deadlocks b/c of the following behavior:
    \*0    1    2    1+K  2+K
    \*|-I->|-U->|... |-L->|
    \*                    U is enabled here, but its missed the deadline, and its not even required
    solution see above
-   Changed the definition of RTBound to accept a requirement predicate called required. Only when 
required holds is the time constraint also required to hold. I set required to be the formula
inserted /\ lastUnlock < unlockTriggerTime
6/11/20 - SN 
-   changed token to Insert in the InsertLeadsToUnlocked property, renamed unlockTimer
*)
EXTENDS Naturals, Sequences, TLC

CONSTANTS MAX_TIME, K

(*TYPES*)
Time == 0..MAX_TIME 

VARIABLE clock   (* what is the current time? *)
VARIABLE locked  (* is the door locked? *)
VARIABLE token   (* is there a token in the reader? *)
VARIABLE open    (* is the door open? *)
VARIABLE lastInsert   (* last time that a card was inserted in reader *)
VARIABLE lastUnlock (* the last time an unlock action took place *)
VARIABLE unlockTriggerTime
VARIABLE lastLock
\*these 2 flags represent the actual actions so must be turned off by every other actions *)
VARIABLE insertAction
VARIABLE unlockAction

(* SYSTEM ACTIONS *)
(* 1. Unlock the Latch  *)
Unlock ==    locked /\ token
          /\ clock <= lastInsert + K \*implements the Unlock => <.>_k Insert /\ token
          /\ locked'=FALSE 
          /\ lastUnlock'=clock 
          /\ insertAction'=FALSE
          /\ unlockAction' =TRUE
          /\ UNCHANGED <<token, open, lastInsert, unlockTriggerTime, lastLock>>
          \*/\ PrintT("@" \o ToString(clock) \o " about to unlock")

(* 2. Lock the Latch *)
Lock == ~locked /\ \*clock > lastInsert+K /\          \*leave it unlocked at least K clock cycles
        lastLock'=clock /\
        locked'=TRUE /\ 
        insertAction'=FALSE /\
        unlockAction' = FALSE /\
        UNCHANGED <<lastUnlock,token, open, lastInsert, unlockTriggerTime>>

(* ENV ACTIONS *)
(* 3. Insert the Token and update lastInsert *)
Insert == ~token
       /\ token'=TRUE
       /\ lastInsert' = clock'
       /\ unlockTriggerTime' = clock'
       /\ insertAction'=TRUE
       /\ unlockAction' = FALSE 
       /\ UNCHANGED <<lastUnlock, locked, open, lastLock>>
       \*/\ PrintT("@" \o ToString(clock) \o " about to insert")

(* 4. Remove the Token *)
Remove == token /\ 
          token'=FALSE /\ insertAction'=FALSE /\ unlockAction' = FALSE /\ \*see comment above re these 
            UNCHANGED <<lastLock, lastUnlock,locked, open, lastInsert, unlockTriggerTime>>

(* 5. Open the Door *)
Open == ~open /\ ~locked /\
        open'=TRUE /\ insertAction'=FALSE /\ unlockAction' = FALSE /\
            UNCHANGED <<lastLock, lastUnlock,locked, token, lastInsert, unlockTriggerTime>>

(* 6. Close the Door *)
Close ==    open /\ 
            open'=FALSE /\ insertAction'=FALSE /\ unlockAction' = FALSE /\ 
                UNCHANGED <<lastLock, lastUnlock, locked, token, lastInsert, unlockTriggerTime>>

(* ACTION CONSTRAINT *)
RTBound(A, v, start, min, max) ==    (* prevents time from progressing after max unless A happens *)
    \*ENABLED is here so the time constraint only applies when its needed, ie A still needs to happn
    LET MaxTime == ENABLED(A) => (clock <= start + max)
        MinTime == A => (clock >= start + min) 
    IN  MaxTime /\ MinTime 
(*
RTBound(required, A, v, start, min, max) ==    (* prevents time from progressing after max unless A happens *)
   LET MaxTime == required => (clock <= start + max)
       MinTime == A => (clock >= start + min) 
   IN  MaxTime /\ MinTime 
*)   

(* --------- the specification of behavior  ----------------- *)

TypeCheck ==      
        clock \in Nat   
     /\ lastInsert \in Time
     /\ lastUnlock \in Time
     /\ lastLock \in Time
     /\ unlockTriggerTime \in Time
     /\ locked \in BOOLEAN 
     /\ token  \in BOOLEAN 
     /\ open   \in BOOLEAN
     /\ insertAction \in BOOLEAN
     /\ unlockAction \in BOOLEAN

Init == clock      = 0
     /\ lastInsert = MAX_TIME (* end of time *)
     /\ lastUnlock = MAX_TIME (* end of time *)
     /\ lastLock = 0    
     /\ unlockTriggerTime = 0
     /\ locked = TRUE
     /\ token = FALSE
     /\ open = FALSE
     /\ TypeCheck
     /\ insertAction=FALSE
     /\ unlockAction=FALSE

vars1 == 
    <<locked, token, open, lastInsert, lastUnlock, unlockTriggerTime, insertAction, lastLock, unlockAction>>
vars == 
    <<locked, token, open, lastInsert, lastUnlock, unlockTriggerTime, insertAction, lastLock, unlockAction, 
        clock>> \*for some reason TLC doesn't like: Append(vars1, clock)
     
ClockTick == clock' = clock+1 \*Now a constraint in the model: IF clock < MAX_TIME THEN clock' = clock+1 ELSE UNCHANGED clock
             
EnvActs == Insert \/ 
           Remove \/
           Open \/ 
           Close
            
SysActs == Unlock \/ 
           Lock 
           
SysOrEnvOrSkip == EnvActs \/ 
                  SysActs \/ 
                  (UNCHANGED vars1 /\ (*see comment at top*) insertAction'=FALSE /\ unlockAction'=FALSE)

\*foo == insertAction /\ lastUnlock < unlockTriggerTime 
CheckTimeConstraint == 
    RTBound(Unlock, <<locked, token, open, lastInsert, lastUnlock, lastLock>>, lastInsert, 1, K-1)
    \* do not want this, allows the system to ignore the RT Bound! / UNCHANGED vars1
    
Next     == /\ ClockTick
            /\ SysOrEnvOrSkip
            /\ CheckTimeConstraint
            
Spec == Init /\ [][Next]_vars 

(* REQUIRED PROPERTIES *)
(* any Unlock action must be preceded by a card Insert within k time units and token is still in*)
\*TLC doesn't like: UnlockPre == [Unlock => (clock <= K + lastInsert)]_vars
\*UnlockPre == unlockAction => clock <= K + lastInsert /\ lastLock < lastInsert
UnlockPre == unlockAction => (clock <= K + lastInsert /\ token)

\*except initially, the essence of this is saying lastUnlock < lastInsert => clock <= lastInsert + K
InsertLeadsToUnlocked == \* was (token => (unlockTriggerTime = clock /\
    \*TLC doesnt like print statements in Properties: PrintT("token=" \o ToString(token) \o ", unlockTriggerTime= " \o ToString(unlockTriggerTime)) /\
    \*TLA doesn't like: Insert => (unlockTriggerTime = clock /\ []...)
    (insertAction => (unlockTriggerTime = clock /\ 
                  [] (lastUnlock < unlockTriggerTime => clock  <= unlockTriggerTime + K)))

THEOREM Spec => []TypeCheck
THEOREM Spec => []InsertLeadsToUnlocked
THEOREM Spec => []UnlockPre

=============================================================================
\* Modification History
\* Last modified Fri Sep 25 13:49:09 PDT 2020 by snedunu
\* Created Thu May 21 11:41:05 PDT 2020 by snedunu
