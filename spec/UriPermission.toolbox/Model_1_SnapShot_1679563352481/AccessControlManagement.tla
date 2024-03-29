---------------------- MODULE AccessControlManagement ----------------------
EXTENDS Naturals, Sequences

CONSTANTS Apps, Perms

NULL == "NULL"
ALLOW == "ALLOW"
REJECT == "REJECT"

Boolean == { TRUE, FALSE }
Consent == { ALLOW, REJECT }

VARIABLE ACL, Resource

TypeOK == /\ \A a \in Apps: \A p \in Perms: /\ ACL[a][p] \in Consent \cup { NULL }
                                            /\ Resource[a][p] \in Boolean

decide(a, p) == /\ \E c \in Consent:
                   ACL' = [ACL EXCEPT ![a] = [ACL[a] EXCEPT ![p] = c]]
                   
use(a, p) == /\ ACL[a][p] = ALLOW
             /\ Resource' = [Resource EXCEPT ![a] = [Resource[a] EXCEPT ![p] = TRUE]]
             /\ UNCHANGED <<ACL>>
                   
ask(a, p) == IF ACL[a][p] = NULL
                THEN /\ decide(a, p)
                     /\ UNCHANGED <<Resource>>
             ELSE
                /\ UNCHANGED <<ACL, Resource>>

clear == /\ ACL' = [a \in Apps |-> [p \in Perms |-> NULL]]
         /\ Resource' = [a \in Apps |-> [p \in Perms |-> FALSE]]

Init == /\ ACL = [a \in Apps |-> [p \in Perms |-> NULL]]
        /\ Resource = [a \in Apps |-> [p \in Perms |-> FALSE]]

Next == \/ \E a \in Apps : \E p \in Perms: \/ ask(a, p)
                                           \/ use(a, p)
        \/ clear

vars == <<ACL, Resource>>

Authorized == [] ~(/\ \E a \in Apps : \E p \in Perms :
                      /\ Resource[a][p] = TRUE
                      /\ ACL[a][p] # ALLOW)

Spec == Init /\ [][Next]_vars /\ Authorized

=============================================================================
\* Modification History
\* Last modified Thu Mar 23 12:47:48 GMT+03:30 2023 by Amirhosein
\* Created Thu Mar 23 07:45:26 GMT+03:30 2023 by Amirhosein
