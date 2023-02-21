------------ MODULE PermissionManager ----------------------------
EXTENDS Naturals

CONSTANTS P, R, A

ASSUME P \in Nat
ASSUME R \in Nat
ASSUME A \in Nat

Permissions == 1..P
Resources == 1..R
Applications == 1..A

PermissionRequestDecision == { "GRANT", "DENY" }
UserConsent == { "ALLOW", "REJECT" }

(***       this is a comment containing the PlusCal code *

--algorithm PermissionManager
{
    variables permissions = [i \in P |-> i];
              resources = [i \in R |-> i];
    fair process (a \in Applications)
    variables unchecked = {}, max = 0, nxt = 1 ;
    { platform:- while (TRUE) 
                 {
                    cs: skip;
                 };
    }
}

    this ends the comment containing the PlusCal code
*************)             
\* BEGIN TRANSLATION (chksum(pcal) = "9c887fbb" /\ chksum(tla) = "7c8cb3da")
VARIABLES permissions, resources, pc, unchecked, max, nxt

vars == << permissions, resources, pc, unchecked, max, nxt >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ permissions = [i \in P |-> i]
        /\ resources = [i \in R |-> i]
        (* Process a *)
        /\ unchecked = [self \in Applications |-> {}]
        /\ max = [self \in Applications |-> 0]
        /\ nxt = [self \in Applications |-> 1]
        /\ pc = [self \in ProcSet |-> "platform"]

platform(self) == /\ pc[self] = "platform"
                  /\ pc' = [pc EXCEPT ![self] = "cs"]
                  /\ UNCHANGED << permissions, resources, unchecked, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "platform"]
            /\ UNCHANGED << permissions, resources, unchecked, max, nxt >>

a(self) == platform(self) \/ cs(self)

Next == (\E self \in Applications: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : WF_vars((pc[self] # "platform") /\ a(self))

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Feb 21 22:47:46 IRST 2023 by Amirhosein
