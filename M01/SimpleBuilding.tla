--------------------------- MODULE SimpleBuilding ---------------------------
(*
  A simple system to maintain a register of users authorised to enter a building
  and to keep track of whether each registered user is in the building or not.
*) 

CONSTANT 
  PERSON                                  (* set of persons *)
  
VARIABLE
  register,                               (* set of registered users *)
  in,                                     (* set of users inside the building *)
  out                                     (* set of users outside the building *)

TypeOk ==
  /\ register \subseteq PERSON            (* Everyone on the register is a person *)
  /\ register = in \union out             (* The location of every registered person is known *)
  /\ in \intersect out = {}               (* Nobody can at the same time be both inside and outside the building *)

----
Init ==
  /\ register = {}                        (* Initially, nobody is registered *)                        
  /\ in = {}
  /\ out = {}
  
Register(p) ==
  /\ p \in PERSON \ register              (* Can only register an unregistered person *)
  /\ register' = register \union {p}      (* The person is added to the register *)
  /\ out' = out \union {p}                (* When first registered, the person is outside the building *)
  /\ in' = in                             (* Registering a person does not change who is inside the building *) 
  
Enter(p) ==
  /\ p \in out                            (* Only registered persons outside the building can enter *)
  /\ in' = in \union {p}                  (* The person is added to the set of persons inside the building *)
  /\ out' = out \ {p}                     (* The person is removed from the set of persons outside the building *)
  /\ register' = register                 (* The register is unchanged *)
  
Leave(p) ==
  /\ p \in in                             (* Only registered persons inside the building can leave *)
  /\ out' = out \union {p}                (* The person is added to the set of persons outside the building *)
  /\ in' = in \ {p}                       (* The person is removed from the set of persons inside the building *)
  /\ register' = register                 (* The register is unchanged *)
  
Next ==                                   (* A Next step is ... *)
  \E p \in PERSON :                       (* for some person ... *) 
    \/ Register(p)                        (* either the person is registered *)
    \/ Enter(p)                           (* or the person enters the building *)
    \/ Leave(p)                           (* or the person leaves the building *)
=============================================================================
\* Modification History
\* Last modified Sun Sep 23 10:56:47 BST 2018 by cgdk2
\* Created Wed Sep 12 12:44:40 BST 2018 by cgdk2
