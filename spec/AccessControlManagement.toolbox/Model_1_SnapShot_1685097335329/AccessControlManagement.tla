---------------------- MODULE AccessControlManagement ----------------------
EXTENDS Naturals, Sequences

CONSTANTS Processes, Resources

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
              Acl2 = [a \in Processes |-> [r \in Resources |-> NULL]];
        
    macro Request(p, r)
    {
     if(Acl[p][r] = NULL)
      Acl[p][r] := REQUESTED;
    }

    macro Decide(p, r)
    {
     if(Acl[p][r] = REQUESTED)
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
     if(Acl[p][r] = ALLOWED)
      Acl[p][r] := NULL;
    }
    
    macro Use(p, r)
    {
     if(Acl[p][r] = ALLOWED)
      Acl[p][r] := IN_USE;
    }
        
    fair process (AcmNext \in Processes)
    variable Resource = 1;
    {
        AcmBegin:- while (TRUE)
        {
         \*with(r \in Resources)
         \*{
         Resource := 1;
         dsd: while(Resource \in Resources)
         {
         Acl2 := Acl;
          either { a: Request(self, Resource); }
          or { b: Decide(self, Resource); }
          or { c: Revoke(self, Resource); }
          or { d: Use(self, Resource); };
          N: Resource:=Resource+1;
          \*}
          }
        };
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "dc5f4776" /\ chksum(tla) = "c727d200")
VARIABLES Acl, Acl2, pc, Resource

vars == << Acl, Acl2, pc, Resource >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ Acl = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Acl2 = [a \in Processes |-> [r \in Resources |-> NULL]]
        (* Process AcmNext *)
        /\ Resource = [self \in Processes |-> 1]
        /\ pc = [self \in ProcSet |-> "AcmBegin"]

AcmBegin(self) == /\ pc[self] = "AcmBegin"
                  /\ Resource' = [Resource EXCEPT ![self] = 1]
                  /\ pc' = [pc EXCEPT ![self] = "dsd"]
                  /\ UNCHANGED << Acl, Acl2 >>

dsd(self) == /\ pc[self] = "dsd"
             /\ IF Resource[self] \in Resources
                   THEN /\ Acl2' = Acl
                        /\ \/ /\ pc' = [pc EXCEPT ![self] = "a"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "b"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "c"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "d"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "AcmBegin"]
                        /\ Acl2' = Acl2
             /\ UNCHANGED << Acl, Resource >>

N(self) == /\ pc[self] = "N"
           /\ Resource' = [Resource EXCEPT ![self] = Resource[self]+1]
           /\ pc' = [pc EXCEPT ![self] = "dsd"]
           /\ UNCHANGED << Acl, Acl2 >>

a(self) == /\ pc[self] = "a"
           /\ IF Acl[self][Resource[self]] = NULL
                 THEN /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = REQUESTED]
                 ELSE /\ TRUE
                      /\ Acl' = Acl
           /\ pc' = [pc EXCEPT ![self] = "N"]
           /\ UNCHANGED << Acl2, Resource >>

b(self) == /\ pc[self] = "b"
           /\ IF Acl[self][Resource[self]] = REQUESTED
                 THEN /\ \E b \in Boolean:
                           IF b = TRUE
                              THEN /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = ALLOWED]
                              ELSE /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = REJECTED]
                 ELSE /\ TRUE
                      /\ Acl' = Acl
           /\ pc' = [pc EXCEPT ![self] = "N"]
           /\ UNCHANGED << Acl2, Resource >>

c(self) == /\ pc[self] = "c"
           /\ IF Acl[self][Resource[self]] = ALLOWED
                 THEN /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = NULL]
                 ELSE /\ TRUE
                      /\ Acl' = Acl
           /\ pc' = [pc EXCEPT ![self] = "N"]
           /\ UNCHANGED << Acl2, Resource >>

d(self) == /\ pc[self] = "d"
           /\ IF Acl[self][Resource[self]] = ALLOWED
                 THEN /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = IN_USE]
                 ELSE /\ TRUE
                      /\ Acl' = Acl
           /\ pc' = [pc EXCEPT ![self] = "N"]
           /\ UNCHANGED << Acl2, Resource >>

AcmNext(self) == AcmBegin(self) \/ dsd(self) \/ N(self) \/ a(self)
                    \/ b(self) \/ c(self) \/ d(self)

Next == (\E self \in Processes: AcmNext(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars((pc[self] # "AcmBegin") /\ AcmNext(self))

\* END TRANSLATION 

AcmTypeOK == /\ Acl \in [Processes -> [Resources -> ResourceStatus]]
             /\ Acl2 \in [Processes -> [Resources -> ResourceStatus]]

AcmConsistent == ~(\E p \in Processes:
                   \E r \in Resources:
                        Acl[p][r] = IN_USE /\ Acl2[p][r] # ALLOWED /\ Acl2[p][r] # IN_USE)

AcmLiveness == <> (\E p \in Processes:
                   \E r \in Resources:
                        Acl[p][r] = REQUESTED ~> Acl[p][r] = ALLOWED \/ Acl[p][r] = REJECTED)

=============================================================================
\* Modification History
\* Last modified Fri May 26 14:05:26 GMT+03:30 2023 by Amirhosein
\* Created Thu Mar 23 07:45:26 GMT+03:30 2023 by Amirhosein
