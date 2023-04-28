---------------------- MODULE AndroidPermissionsSystem ----------------------
EXTENDS Naturals, Sequences

CONSTANT Apps

(***

--algorithm PermissionManager
{
    variables A = [p \in Apps |-> FALSE];
    
    fair process (a \in Apps)
    {
        PLATFORM:- while (TRUE)
        {
            A[self] := TRUE;
        };
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "4a3f5cf4" /\ chksum(tla) = "67a4a844")
VARIABLES A, pc

vars == << A, pc >>

ProcSet == (Apps)

Init == (* Global variables *)
        /\ A = [p \in Apps |-> FALSE]
        /\ pc = [self \in ProcSet |-> "PLATFORM"]

PLATFORM(self) == /\ pc[self] = "PLATFORM"
                  /\ A' = [A EXCEPT ![self] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "PLATFORM"]

a(self) == PLATFORM(self)

Next == (\E self \in Apps: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Apps : WF_vars((pc[self] # "PLATFORM") /\ a(self))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Apr 28 09:01:44 GMT+03:30 2023 by Amirhosein
\* Created Fri Apr 28 08:40:56 GMT+03:30 2023 by Amirhosein
