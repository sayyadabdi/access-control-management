---------------------- MODULE AccessControlManagement ----------------------
EXTENDS Naturals, Sequences

CONSTANTS Apps, Perms

NULL == "NULL"
ALLOW == "ALLOW"
REJECT == "REJECT"

Boolean == { TRUE, FALSE }
Consent == { ALLOW, REJECT, NULL }

VARIABLE ACL, Resource

TypeOK == \A a \in Apps: \A p \in Perms: ACL[a][p] \in Consent

decide(a, p) == /\ ACL[a][p] = NULL
                /\ \E c \in Consent:
                   ACL' = [ACL EXCEPT ![a] = [ACL[a] EXCEPT ![p] = c]]
                   
use(a, p) == /\ ACL[a][p] = ALLOW
             /\ Resource' = [Resource EXCEPT ![p] = [ACL[p] EXCEPT ![a] = TRUE]]
             /\ UNCHANGED <<ACL>>
                   
ask(a, p) == IF ACL[a][p] = NULL
                THEN /\ decide(a, p)
                     /\ UNCHANGED <<Resource>>
             ELSE
                UNCHANGED <<ACL, Resource>>

Init == /\ ACL = [a \in Apps |-> [p \in Perms |-> NULL]]
        /\ Resource = [p \in Perms |-> [a \in Apps |-> Boolean]]

Next == /\ ACL # [Apps |-> [Perms |-> NULL]]
        /\ \E a \in Apps : \E p \in Perms: \/ ask(a, p)
                                           \/ use(a, p)

vars == <<ACL, Resource>>

Authorized == [] ~(/\ \E a \in Apps : \E p \in Perms :
                      /\ Resource[p][a] = TRUE
                      /\ Apps[a][p] # ALLOW)

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Thu Mar 23 09:29:42 GMT+03:30 2023 by Amirhosein
\* Created Thu Mar 23 07:45:26 GMT+03:30 2023 by Amirhosein
