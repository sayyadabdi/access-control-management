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
        s0: while(TRUE)
        {
         s1: Resource := 1;
         s2: Acl2 := Acl;
         
         either { a: Request(self, Resource); }
         or { b: Decide(self, Resource); }
         or { c: Revoke(self, Resource); }
         or { d: Use(self, Resource); };
         
         N: Resource := Resource + 1;
         
         if(Resource \in Resources)
          goto s1;
        }
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "815326e1" /\ chksum(tla) = "5b152e55")
VARIABLES Acl, Acl2, pc, Resource

vars == << Acl, Acl2, pc, Resource >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ Acl = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Acl2 = [a \in Processes |-> [r \in Resources |-> NULL]]
        (* Process AcmNext *)
        /\ Resource = [self \in Processes |-> 1]
        /\ pc = [self \in ProcSet |-> "s0"]

s0(self) == /\ pc[self] = "s0"
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << Acl, Acl2, Resource >>

s1(self) == /\ pc[self] = "s1"
            /\ Resource' = [Resource EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << Acl, Acl2 >>

s2(self) == /\ pc[self] = "s2"
            /\ Acl2' = Acl
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "a"]
               \/ /\ pc' = [pc EXCEPT ![self] = "b"]
               \/ /\ pc' = [pc EXCEPT ![self] = "c"]
               \/ /\ pc' = [pc EXCEPT ![self] = "d"]
            /\ UNCHANGED << Acl, Resource >>

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

N(self) == /\ pc[self] = "N"
           /\ Resource' = [Resource EXCEPT ![self] = Resource[self] + 1]
           /\ IF Resource'[self] \in Resources
                 THEN /\ pc' = [pc EXCEPT ![self] = "s1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "s0"]
           /\ UNCHANGED << Acl, Acl2 >>

AcmNext(self) == s0(self) \/ s1(self) \/ s2(self) \/ a(self) \/ b(self)
                    \/ c(self) \/ d(self) \/ N(self)

Next == (\E self \in Processes: AcmNext(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(AcmNext(self))

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
\* Last modified Fri May 26 14:23:17 GMT+03:30 2023 by Amirhosein
\* Created Thu Mar 23 07:45:26 GMT+03:30 2023 by Amirhosein
