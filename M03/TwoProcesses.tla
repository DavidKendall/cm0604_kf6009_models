----------------------------- MODULE TwoProcesses -----------------------------
(*
--algorithm TwoProcesses
  variable
    x = 0,
    y = 0
    
    
  process P1 = "x"
  begin
x1: if y = 0 then
      x := 1
    end if
  end process
  
  process P2 = "y"
  begin
y1: if x = 0 then
      y := 1
    end if
  end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == {"x"} \cup {"y"}

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ pc = [self \in ProcSet |-> CASE self = "x" -> "x1"
                                        [] self = "y" -> "y1"]

x1 == /\ pc["x"] = "x1"
      /\ IF y = 0
            THEN /\ x' = 1
            ELSE /\ TRUE
                 /\ x' = x
      /\ pc' = [pc EXCEPT !["x"] = "Done"]
      /\ y' = y

P1 == x1

y1 == /\ pc["y"] = "y1"
      /\ IF x = 0
            THEN /\ y' = 1
            ELSE /\ TRUE
                 /\ y' = y
      /\ pc' = [pc EXCEPT !["y"] = "Done"]
      /\ x' = x

P2 == y1

Next == P1 \/ P2
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Tue Oct 23 12:05:57 BST 2018 by cgdk2
\* Created Fri Oct 19 11:50:24 BST 2018 by cgdk2
