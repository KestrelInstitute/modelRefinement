----------------------------- MODULE TokeneerI -----------------------------
(*History
04/20/21 - SN - created by simplifying TokeneerDS
*)
EXTENDS Naturals, Sequences, TLC

(*TYPES*)

VARIABLE locked     (* is the door locked? *)
VARIABLE token      (* is there a token in the reader? *)
VARIABLE open       (* is the door open? *)

(* SYSTEM ACTIONS *)
(* 1. Unlock the Latch  *)
Unlock ==
       locked \*this needed at this stage? /\ token
    /\ locked'=FALSE /\ UNCHANGED <<token, open>>

(* 2. Lock the Latch *)
Lock ==
       ~locked \*this needed at this stage? /\ token
    /\ locked'=TRUE /\ UNCHANGED <<token, open>>

(* ENV ACTIONS *)
(* 3. Insert the Token *)
Insert == 
        ~token
    /\  token'=TRUE /\ UNCHANGED <<locked, open>>

(* 4. Remove the Token *)
Remove == 
        token
    /\  token'=FALSE /\ UNCHANGED <<locked, open>>

(*
(* 5. Open the Door *)
Open == 
        ~open /\ ~locked
    /\  open'=TRUE /\ UNCHANGED <<locked, token>>

(* 6. Close the Door *)
Close ==
        open
    /\  open'=FALSE /\ UNCHANGED <<locked, token>>
*)

(* --------- the specification of behavior  ----------------- *)
TypeCheck ==      
     /\ locked \in BOOLEAN 
     /\ token  \in BOOLEAN 
     /\ open   \in BOOLEAN

Init ==
     /\ locked = TRUE
     /\ token = FALSE
     /\ open = FALSE
     /\ TypeCheck

vars == <<locked, token, open>>
     
EnvActs == 
    \/  Insert 
    \/  Remove
\*    \/  Open
\*    \/  Close
            
SysActs == 
        Unlock
    \/  Lock
           
SysOrEnvOrSkip == 
    EnvActs \/ SysActs
    
Next == 
    SysOrEnvOrSkip
            
Spec == Init /\ [][Next]_vars

(* REQUIRED PROPERTIES - Don't hold at this level *)
(* any Unlock action must be preceded by a card Insert within k time units and token is still in*)
\*UnlockPre == Unlock => (<_>_K Insert) /\ token

\*InsertLeadsToUnlocked == Insert => (<>_K Unlock)

THEOREM Spec => []TypeCheck
\*THEOREM Spec => []InsertLeadsToUnlocked
\*THEOREM Spec => []UnlockPre

=============================================================================
\* Modification History
\* Last modified Thu Apr 29 16:29:38 PDT 2021 by snedunu
\* Created Thu May 21 11:41:05 PDT 2020 by snedunu
