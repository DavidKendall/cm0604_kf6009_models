---- MODULE PCalBuilding ----
CONSTANT
  PERSON,
  BUILDING

  OUTSIDE == CHOOSE x : x \notin PERSON \union BUILDING

(*
--algorithm PCalBuilding
  variable
    register = {};
    permission = << >>;
    location = << >>;

                begin
L1:               either
Register:           with p \in PERSON \ register do
                      register := register \union {p};
		      permission := [x \in DOMAIN permission \union {p} |->
		                      IF x\in DOMAIN permission THEN permission[x] ELSE {}];
                      location := [x \in DOMAIN location \union {p} |-> 
                                    IF x \in DOMAIN location THEN location[x] ELSE OUTSIDE];
                    end with
		  or
DeRegister:         with p \in register do
                      register := register \ {p};
		      permission := [x \in register |-> permission[x]];
		      location := [x \in register |-> location[x]];
		    end with
                  or 
RevokePermission:   with p \in register, b \in permission[p] do
                      permission[p] := permission[p] \ {b};
		      if location[p] = b then 
		        location[p] := OUTSIDE;
		      end if
		    end with
	          end either
                end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES register, permission, location, pc

vars == << register, permission, location, pc >>

Init == (* Global variables *)
        /\ register = {}
        /\ permission = << >>
        /\ location = << >>
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ \/ /\ pc' = "Register"
         \/ /\ pc' = "DeRegister"
         \/ /\ pc' = "RevokePermission"
      /\ UNCHANGED << register, permission, location >>

Register == /\ pc = "Register"
            /\ \E p \in PERSON \ register:
                 /\ register' = (register \union {p})
                 /\ permission' = [x \in DOMAIN permission \union {p} |->
                                    IF x\in DOMAIN permission THEN permission[x] ELSE {}]
                 /\ location' = [x \in DOMAIN location \union {p} |->
                                  IF x \in DOMAIN location THEN location[x] ELSE OUTSIDE]
            /\ pc' = "Done"

DeRegister == /\ pc = "DeRegister"
              /\ \E p \in register:
                   /\ register' = register \ {p}
                   /\ permission' = [x \in register' |-> permission[x]]
                   /\ location' = [x \in register' |-> location[x]]
              /\ pc' = "Done"

RevokePermission == /\ pc = "RevokePermission"
                    /\ \E p \in register:
                         \E b \in permission[p]:
                           /\ permission' = [permission EXCEPT ![p] = permission[p] \ {b}]
                           /\ IF location[p] = b
                                 THEN /\ location' = [location EXCEPT ![p] = OUTSIDE]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED location
                    /\ pc' = "Done"
                    /\ UNCHANGED register

Next == L1 \/ Register \/ DeRegister \/ RevokePermission
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

====
