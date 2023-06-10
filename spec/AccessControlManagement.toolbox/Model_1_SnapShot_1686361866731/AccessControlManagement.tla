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
              Consent = [a \in Processes |-> [r \in Resources |-> FALSE]];
              Grid = [a \in Processes |-> [a2 \in Processes |-> FALSE]];
        
    macro Request(p, r) { Acl[p][r] := REQUESTED; }

    macro Decide(p, r)
    {
      with(b \in Boolean)
      {
       if(b = TRUE)
       {
        Acl[p][r] := ALLOWED;
        Consent[p][r] := TRUE;
       }
       else
       {
        Acl[p][r] := REJECTED;
        Consent[p][r] := FALSE;
       }
      }
    }
    
    macro Revoke(p, r)
    {
      Acl[p][r] := NULL;
      Consent[p][r] := FALSE;
    }
    
    macro Use(p, r)
    {
      Acl[p][r] := IN_USE;
    }
    
    macro Connect(a1, a2)
    {
     Grid[a1][a2] := TRUE;
    }
    
    procedure Delegate(app1, app2)
    variable ResourceList = Resources;
    {
     DELEGATE:
     while(ResourceList # {})
     {
      with(r \in ResourceList)
      {
       if(Acl[app2][r] = ALLOWED)
        Acl[app1][r] := ALLOWED;
        
       ResourceList := ResourceList \ {r};
      }
     };
     return;
    }
        
    fair process (AcmNext \in Processes)
    variable Resource
    {
        s0: Grid[self][self] := TRUE;
        
        s1: while(TRUE)
        {
         s2: with (R \in Resources) { Resource := R; };
         
         s3: if(Acl[self][Resource] = NULL) { Request(self, Resource); }
         
             else if(Acl[self][Resource] = REQUESTED) { Decide(self, Resource); }
             
             else if(Acl[self][Resource] = ALLOWED)
             {
              either { Revoke(self, Resource); }
              or { Use(self, Resource); }
             };
             
         s4: with (rand \in Boolean)
         {
          if(rand = TRUE)
          {
           with (a \in (Processes \ {self}))
           {
            Connect(self, a);
            call Delegate(self, a);
           }
          }
         }
        }
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "9e7f69c5" /\ chksum(tla) = "61795fd0")
CONSTANT defaultInitValue
VARIABLES Acl, Consent, Grid, pc, stack, app1, app2, ResourceList, Resource

vars == << Acl, Consent, Grid, pc, stack, app1, app2, ResourceList, Resource
        >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ Acl = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Consent = [a \in Processes |-> [r \in Resources |-> FALSE]]
        /\ Grid = [a \in Processes |-> [a2 \in Processes |-> FALSE]]
        (* Procedure Delegate *)
        /\ app1 = [ self \in ProcSet |-> defaultInitValue]
        /\ app2 = [ self \in ProcSet |-> defaultInitValue]
        /\ ResourceList = [ self \in ProcSet |-> Resources]
        (* Process AcmNext *)
        /\ Resource = [self \in Processes |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "s0"]

DELEGATE(self) == /\ pc[self] = "DELEGATE"
                  /\ IF ResourceList[self] # {}
                        THEN /\ \E r \in ResourceList[self]:
                                  /\ IF Acl[app2[self]][r] = ALLOWED
                                        THEN /\ Acl' = [Acl EXCEPT ![app1[self]][r] = ALLOWED]
                                        ELSE /\ TRUE
                                             /\ Acl' = Acl
                                  /\ ResourceList' = [ResourceList EXCEPT ![self] = ResourceList[self] \ {r}]
                             /\ pc' = [pc EXCEPT ![self] = "DELEGATE"]
                             /\ UNCHANGED << stack, app1, app2 >>
                        ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ ResourceList' = [ResourceList EXCEPT ![self] = Head(stack[self]).ResourceList]
                             /\ app1' = [app1 EXCEPT ![self] = Head(stack[self]).app1]
                             /\ app2' = [app2 EXCEPT ![self] = Head(stack[self]).app2]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ Acl' = Acl
                  /\ UNCHANGED << Consent, Grid, Resource >>

Delegate(self) == DELEGATE(self)

s0(self) == /\ pc[self] = "s0"
            /\ Grid' = [Grid EXCEPT ![self][self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << Acl, Consent, stack, app1, app2, ResourceList, 
                            Resource >>

s1(self) == /\ pc[self] = "s1"
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << Acl, Consent, Grid, stack, app1, app2, 
                            ResourceList, Resource >>

s2(self) == /\ pc[self] = "s2"
            /\ \E R \in Resources:
                 Resource' = [Resource EXCEPT ![self] = R]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << Acl, Consent, Grid, stack, app1, app2, 
                            ResourceList >>

s3(self) == /\ pc[self] = "s3"
            /\ IF Acl[self][Resource[self]] = NULL
                  THEN /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = REQUESTED]
                       /\ UNCHANGED Consent
                  ELSE /\ IF Acl[self][Resource[self]] = REQUESTED
                             THEN /\ \E b \in Boolean:
                                       IF b = TRUE
                                          THEN /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = ALLOWED]
                                               /\ Consent' = [Consent EXCEPT ![self][Resource[self]] = TRUE]
                                          ELSE /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = REJECTED]
                                               /\ Consent' = [Consent EXCEPT ![self][Resource[self]] = FALSE]
                             ELSE /\ IF Acl[self][Resource[self]] = ALLOWED
                                        THEN /\ \/ /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = NULL]
                                                   /\ Consent' = [Consent EXCEPT ![self][Resource[self]] = FALSE]
                                                \/ /\ Acl' = [Acl EXCEPT ![self][Resource[self]] = IN_USE]
                                                   /\ UNCHANGED Consent
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << Acl, Consent >>
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << Grid, stack, app1, app2, ResourceList, Resource >>

s4(self) == /\ pc[self] = "s4"
            /\ \E rand \in Boolean:
                 IF rand = TRUE
                    THEN /\ \E a \in (Processes \ {self}):
                              /\ Grid' = [Grid EXCEPT ![self][a] = TRUE]
                              /\ /\ app1' = [app1 EXCEPT ![self] = self]
                                 /\ app2' = [app2 EXCEPT ![self] = a]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Delegate",
                                                                          pc        |->  "s1",
                                                                          ResourceList |->  ResourceList[self],
                                                                          app1      |->  app1[self],
                                                                          app2      |->  app2[self] ] >>
                                                                      \o stack[self]]
                              /\ ResourceList' = [ResourceList EXCEPT ![self] = Resources]
                              /\ pc' = [pc EXCEPT ![self] = "DELEGATE"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "s1"]
                         /\ UNCHANGED << Grid, stack, app1, app2, ResourceList >>
            /\ UNCHANGED << Acl, Consent, Resource >>

AcmNext(self) == s0(self) \/ s1(self) \/ s2(self) \/ s3(self) \/ s4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Delegate(self))
           \/ (\E self \in Processes: AcmNext(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(AcmNext(self)) /\ WF_vars(Delegate(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

AcmTypeOK == /\ Acl \in [Processes -> [Resources -> ResourceStatus]]
             /\ Consent \in [Processes -> [Resources -> Boolean]]
             /\ Grid \in [Processes -> [Processes -> Boolean]]


AcmConsistent == ~(\E p \in Processes:
                   \E r \in Resources:
                      /\ Acl[p][r] = IN_USE
                      /\ Consent[p][r] # TRUE)

AcmLiveness == <> (\E p \in Processes:
                   \E r \in Resources:
                      Acl[p][r] = ALLOWED \/ Acl[p][r] = REJECTED)

=============================================================================
\* Modification History
\* Last modified Fri Jun 09 22:29:27 GMT+03:30 2023 by Amirhosein
\* Created Thu Mar 23 07:45:26 GMT+03:30 2023 by Amirhosein
