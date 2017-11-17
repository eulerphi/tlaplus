-------------------------------- MODULE gset --------------------------------
(*
    Models a grow-only CRDT counter with lossy message delivery.
*)
EXTENDS Integers, Sequences

CONSTANT N, MaxCounter

(*
    nState   = [ "n1": [ "n1": 0, "n2": 0, ..., "nk": 0 ],
                 "n2": [ "n1": 0, "n2": 0, ..., "nk": 0 ],
                 ...,
                 "nk": [ "n1": 0, "n2": 0, ..., "nk": 0 ] ]
    stopIncr = should disable Increment action?
*)
VARIABLE  nState, stopIncr
vars == <<nState, stopIncr>>

Max(m, n) ==
    IF m < n THEN n ELSE m

MergeState(s1, s2) ==
    [n \in N |-> Max(s1[n], s2[n])]

Gossip(n) ==
    /\ \E m \in (N \ { n }):
        nState' = [nState EXCEPT ![m] = MergeState(nState[n], nState[m])]
    /\ UNCHANGED <<stopIncr>>

Init ==
    /\ nState = [n1 \in N |-> [n2 \in N |-> 0]]
    /\ stopIncr = FALSE

Increment(n) ==
    /\ stopIncr = FALSE
    /\ nState[n][n] < MaxCounter
    /\ \E M \in SUBSET N:
        nState' = [m \in N |->
            IF (m = n) \/ (m \in M)
            THEN [nState[m] EXCEPT ![n] = nState[m][n] + 1]
            ELSE nState[m]]
    /\ UNCHANGED <<stopIncr>>


StopIncrementing ==
    /\ stopIncr = FALSE
    /\ stopIncr' = TRUE
    /\ UNCHANGED <<nState>>
    
Converges ==
    /\ (stopIncr = TRUE) ~> (\A n1, n2 \in N: nState[n1] = nState[n2])
                             
Next == \E n \in N :
    \/ Increment(n)
    \/ StopIncrementing
    \/ Gossip(n)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A n \in N: WF_vars(Gossip(n))
    
    

=============================================================================
\* Modification History
\* Last modified Fri Nov 17 22:07:00 UTC 2017 by eulerphi
\* Created Thu Nov 16 21:31:25 UTC 2017 by eulerphi
