------------------------------ MODULE PDieHard ------------------------------
EXTENDS Integers

Min(m, n) == IF m < n THEN m ELSE n

(*
--algorithm PDieHard 
  variable
    big = 0;
    small = 0;
  begin  
    while TRUE do
      either big := 5                               \* Fill big
          or small := 3                             \* Fill small
          or big := 0                               \* Empty big
          or small := 0                             \* Empty small
          or with poured = Min(5 - big, small) do   \* small to big
               big := big + poured;
               small := small - poured
             end with
          or with poured = Min(3 - small, big) do   \* big to small
               small := small + poured;
               big := big - poured
             end with
      end either
    end while
  end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES big, small

vars == << big, small >>

Init == (* Global variables *)
        /\ big = 0
        /\ small = 0

Next == \/ /\ big' = 5
           /\ small' = small
        \/ /\ small' = 3
           /\ big' = big
        \/ /\ big' = 0
           /\ small' = small
        \/ /\ small' = 0
           /\ big' = big
        \/ /\ LET poured == Min(5 - big, small) IN
                /\ big' = big + poured
                /\ small' = small - poured
        \/ /\ LET poured == Min(3 - small, big) IN
                /\ small' = small + poured
                /\ big' = big - poured

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Oct 14 17:34:04 BST 2018 by cgdk2
\* Created Sat Apr 14 13:06:20 BST 2018 by cgdk2
