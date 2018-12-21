---------------------------- MODULE BankAccount ----------------------------
EXTENDS Integers

(*
--algorithm BankAccount
    variable balance = 100;
    
    process Withdraw10 \in 1..2
      variable current = 0;
    begin  
s1:   current := balance;
s2:   current := current - 10;
s3:   balance := current;
    end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES balance, pc, current

vars == << balance, pc, current >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ balance = 100
        (* Process Withdraw10 *)
        /\ current = [self \in 1..2 |-> 0]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ current' = [current EXCEPT ![self] = balance]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED balance

s2(self) == /\ pc[self] = "s2"
            /\ current' = [current EXCEPT ![self] = current[self] - 10]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED balance

s3(self) == /\ pc[self] = "s3"
            /\ balance' = current[self]
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED current

Withdraw10(self) == s1(self) \/ s2(self) \/ s3(self)

Next == (\E self \in 1..2: Withdraw10(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

BalanceOk == (pc[1] = "Done" /\ pc[2] = "Done") => (balance = 80)
=============================================================================
\* Modification History
\* Last modified Mon Oct 15 09:10:33 BST 2018 by cgdk2
\* Created Wed Oct 10 09:43:04 BST 2018 by cgdk2
