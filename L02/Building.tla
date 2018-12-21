------------------------------ MODULE Building ------------------------------
CONSTANT
  PERSON,
  BUILDING
  
  OUTSIDE == CHOOSE x : x \notin PERSON \union BUILDING
  
VARIABLE
  register,
  permission,
  location
  
TypeOk ==
  /\ register \subseteq PERSON
  /\ permission \in [register -> SUBSET BUILDING]
  /\ location \in [register -> (BUILDING \union {OUTSIDE})]
                         
----

Init ==
  /\ register = {}
  /\ permission = << >>
  /\ location = << >>
    
Register(p) ==
  /\ p \in PERSON \ register
  /\ register' = register \union {p}
  /\ permission' = [x \in DOMAIN permission \union {p} |->
                    IF x \in DOMAIN permission THEN permission[x] ELSE {}]
  /\ location' = [x \in DOMAIN location \union {p} |-> 
                  IF x \in DOMAIN location THEN location[x] ELSE OUTSIDE]
  
DeRegister(p) ==
  /\ p \in register
  /\ register' = register \ {p}
  /\ permission' = [x \in register \ {p} |-> permission[x]]
  /\ location' = [x \in register \ {p} |-> location[x]]
  
AddPermission(p, b) ==
  /\ p \in register
  /\ b \in BUILDING \ permission[p]
  /\ permission' = [permission EXCEPT ![p] = permission[p] \union {b}]
  /\ UNCHANGED <<register, location>>
  
RevokePermission(p, b) ==
  /\ p \in register
  /\ b \in permission[p]
  /\ permission' = [permission EXCEPT ![p] = permission[p] \ {b}]
  /\ location' = IF location[p] /= b
                 THEN location
                 ELSE [location EXCEPT ![p] = OUTSIDE] 
  /\ UNCHANGED register
  
Enter(p, b) ==
  /\ p \in register
  /\ b \in permission[p]
  /\ location' = [location EXCEPT ![p] = b]
  /\ UNCHANGED <<register, permission>>
  
Leave(p, b) ==
  /\ p \in register
  /\ location[p] = b
  /\ location' = [location EXCEPT ![p] = OUTSIDE]
  /\ UNCHANGED <<register, permission>>
----

Next == \E p \in PERSON, b \in BUILDING : 
          \/ Register(p) 
          \/ DeRegister(p)
          \/ AddPermission(p, b)
          \/ RevokePermission(p, b)
          \/ Enter(p, b)
          \/ Leave(p, b)

Spec == Init /\ [][Next]_<<register, permission, location>>

----
MustBeRegisteredToHaveLocation ==
  /\ \A p \in PERSON \ register : p \notin DOMAIN location
  
MustBeRegisteredToHavePermission ==
  /\ \A p \in PERSON \ register : p \notin DOMAIN permission
  
MustHavePermissionWhenInBuilding ==
  /\ \A p \in register : \/ location[p] \in permission[p]
                         \/ location[p] = OUTSIDE
                         
GeneralPermission ==
  /\ \A p \in PERSON, b \in BUILDING :
       \/ /\ p \in DOMAIN location 
          /\ location[p] = b => b \in permission[p] 
       \/ p \notin DOMAIN location
       
AlternativePermission ==
  /\ \A p \in PERSON :
       \/ /\ p \in register
          /\ \/ location[p] \in permission[p]
             \/ location[p] = OUTSIDE
       \/ /\ p \notin register
          /\ p \notin DOMAIN location
          /\ p \notin DOMAIN permission 
=============================================================================
\* Modification History
\* Last modified Sun Oct 14 10:26:00 BST 2018 by cgdk2
\* Created Mon Jun 04 15:17:18 BST 2018 by cgdk2
