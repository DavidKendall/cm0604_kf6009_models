-------------------------- MODULE WolfSheepCabbage --------------------------
PARTICIPANTS == {"farmer", "wolf", "sheep", "cabbage"}
BANK == {"left", "right"}

VARIABLE
  location

TypeOk == 
  /\ location \in [PARTICIPANTS -> BANK]
----

Opposite(b) == IF b = "left" THEN "right" ELSE "left"

EverythingSafe(loc) ==
 /\ (loc["wolf"] = loc["sheep"]) => (loc["farmer"] = loc["sheep"])
 /\ (loc["sheep"] = loc["cabbage"]) => (loc["farmer"] = loc["cabbage"]) 
 
Init ==
  /\ location = [p \in PARTICIPANTS |-> "left"]

CrossAlone == 
  /\ location' = [location EXCEPT !["farmer"] = Opposite(location["farmer"])]
  /\ EverythingSafe(location')
  
CrossWith(p) ==
  LET b == location["farmer"] IN
    /\ location[p] = b
    /\ location' = [location EXCEPT ![p] = Opposite(b), !["farmer"] = Opposite(b)]
    /\ EverythingSafe(location')
  
Next == 
  \/ CrossAlone
  \/ \E p \in PARTICIPANTS \ {"farmer"} :
       \/ CrossWith(p)
          
Goal == \A p \in PARTICIPANTS : location[p] = "right"

(*
 * A solution to the problem can be found with the model above by
 * checking the invariant ~Goal and examining the error trace.
 * Alternatively, the behaviour of the model can be less constrained
 * by removing EverythingSafe(location') from CrossAlone and CrossWith(p)
 * and checking the temporal property ([]EverythingSafe(location)) => ([]~Goal)
 *)
 

=============================================================================
\* Modification History
\* Last modified Sun Oct 07 11:44:31 BST 2018 by cgdk2
\* Created Wed Oct 03 10:21:23 BST 2018 by cgdk2
