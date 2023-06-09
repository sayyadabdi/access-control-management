---------------------- MODULE AccessControlManagement ----------------------
EXTENDS Naturals, Sequences

CONSTANTS ProcessCount, ResourceCount

Processes == 1..ProcessCount
Resources == 1..ResourceCount

NULL == "NULL"
ALLOWED == "ALLOWED"
REJECTED == "REJECTED"
REQUESTED == "REQUESTED"
IN_USE == "IN_USE"

Boolean == { TRUE, FALSE }
ResourceStatus == { NULL, REQUESTED, ALLOWED, REJECTED, IN_USE }

(***--algorithm AccessControlManagement
{
    variables Acl = [a \in Processes |-> [r \in Resources |-> NULL]];
              AclHistory = [a \in Processes |-> [r \in Resources |-> NULL]];
        
    macro Request(p, r) { Acl[p][r] := REQUESTED; }

    macro Decide(p, r)
    {
      with(b \in Boolean)
      {
       if(b = TRUE)
        Acl[p][r] := ALLOWED;
       else
        Acl[p][r] := REJECTED;
      }
    }
    
    macro Revoke(p, r)
    {
      Acl[p][r] := NULL;
    }
    
    macro Use(p, r)
    {
      Acl[p][r] := IN_USE;
    }
        
    fair process (AcmNext \in Processes)
    variable Resource
    {
        s1: while(TRUE)
        {
         s2: with (R \in Resources) { Resource := R; };
         
         s3: if(Acl[self][Resource] = NULL) { Request(self, Resource); }
         
             else if(Acl[self][Resource] = REQUESTED) { Decide(self, Resource); }
             
             else if(Acl[self][Resource] = ALLOWED)
             {
              either { Revoke(self, Resource); }
              or { Use(self, Resource); }
             }
        }
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "c6edf9e4" /\ chksum(tla) = "6ab18e11")
CONSTANT defaultInitValue
VARIABLES Acl, AclHistory, pc, Resource

vars == << Acl, AclHistory, pc, Resource >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ Acl = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ AclHistory = [a \in Processes |-> [r \in Resources |-> NULL]]
        (* Process AcmNext *)
        /\ Resource = [self \in Processes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "s1"]

s1(self) == /\ pc[self] = "s1"
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << Acl, AclHistory, Resource >>

s2(self) == /\ pc[self] = "s2"
            /\ \E R \in Resources:
                 Resource' = [Resource EXCEPT ![self] = R]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << Acl, AclHistory >>

s3(self) == /\ pc[self] = "s3"
            /\ IF Acl[self][Resource[self]] = NULL
                  THEN /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = REQUESTED]
                  ELSE /\ IF Acl[self][Resource[self]] = REQUESTED
                             THEN /\ \E b \in Boolean:
                                       IF b = TRUE
                                          THEN /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = ALLOWED]
                                          ELSE /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = REJECTED]
                             ELSE /\ IF Acl[self][Resource[self]] = ALLOWED
                                        THEN /\ \/ /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = NULL]
                                                \/ /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = IN_USE]
                                        ELSE /\ TRUE
                                             /\ Acl' = Acl
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << AclHistory, Resource >>

AcmNext(self) == s1(self) \/ s2(self) \/ s3(self)

Next == (\E self \in Processes: AcmNext(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(AcmNext(self))

\* END TRANSLATION 

AcmTypeOK == /\ Acl \in [Processes -> [Resources -> ResourceStatus]]
             \* /\ Acl2 \in [Processes -> [Resources -> ResourceStatus]]


AcmConsistent == ~(\E p \in Processes:
                   \E r \in Resources:
                      Acl[p][r] = IN_USE)
                 \/ TRUE

AcmLiveness == <> (\E p \in Processes:
                   \E r \in Resources:
                      Acl[p][r] = ALLOWED \/ Acl[p][r] = REJECTED)

=============================================================================
\* Modification History
\* Last modified Fri Jun 09 20:01:47 GMT+03:30 2023 by Amirhosein
\* Created Thu Mar 23 07:45:26 GMT+03:30 2023 by Amirhosein
