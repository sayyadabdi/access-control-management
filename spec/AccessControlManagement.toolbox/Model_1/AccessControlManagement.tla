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

URI_PERMISSION == "URI_PERMISSION"
CUSTOM_PERMISSION == "CUSTOM_PERMISSION"

NORMAL == "NORMAL"
SIGNATURE == "SIGNATURE"
DANGEROUS == "DANGEROUS"

Boolean == { TRUE, FALSE }
ResourceStatus == { REQUESTED, ALLOWED, REJECTED, IN_USE }
PermissionTypes == { URI_PERMISSION, CUSTOM_PERMISSION }
PermissionLevels == { NORMAL, SIGNATURE, DANGEROUS }

(***--algorithm AccessControlManagement
{
    variables Acl_Status = [a \in Processes |-> [r \in Resources |-> NULL]];
              Acl_PermissionType = [a \in Processes |-> [r \in Resources |-> NULL]];
              Acl_PermissionLevel = [a \in Processes |-> [r \in Resources |-> NULL]];
              Consent = [a \in Processes |-> [r \in Resources |-> FALSE]];
              Grid = [a \in Processes |-> [a2 \in Processes |-> FALSE]];

    macro Define(p, r)
    {
     with(t \in PermissionTypes) { Acl_PermissionType[p][r] := t; };
     Acl_PermissionLevel[p][r] := NORMAL;
    }

    macro Request(p, r) { Acl_Status[p][r] := REQUESTED; }

    macro Decide(p, r)
    {
      with(b \in Boolean)
      {
       if(b = TRUE)
       {
        Acl_Status[p][r] := ALLOWED;
        Consent[p][r] := TRUE;
       }
       else
       {
        Acl_Status[p][r] := REJECTED;
        Consent[p][r] := FALSE;
       }
      }
    }
    
    macro Revoke(p, r)
    {
      Acl_Status[p][r] := NULL;
      Consent[p][r] := FALSE;
    }
    
    macro Use(p, r)
    {
      Acl_Status[p][r] := IN_USE;
    }
    
    macro Connect(a1, a2)
    {
     Grid[a1][a2] := TRUE;
    }
    
    procedure Update(p2)
    variable ResourceList = Resources;
    {
     UPDATE:
     while(ResourceList # {})
     {
      with(r \in ResourceList)
      {
       if(Acl_PermissionLevel[p2][r] = NORMAL)
       {
        Acl_PermissionLevel[p2][r] := DANGEROUS;
        Consent[p2][r] := FALSE;
       };
        
       ResourceList := ResourceList \ {r};
      }
     };
     return;
    }
    
    procedure Delegate(app1, app2)
    variable ResourceList = Resources;
    {
     DELEGATE:
     while(ResourceList # {})
     {
      with(r \in ResourceList)
      {
       if(Acl_PermissionType[app2][r] # NULL /\ Acl_PermissionType[app1][r] = NULL)
        Acl_PermissionType[app1][r] := Acl_PermissionType[app2][r];
       
       if(Acl_Status[app2][r] # NULL /\ Acl_Status[app1][r] = NULL)
        Acl_Status[app1][r] := Acl_Status[app2][r];
        
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
         
         s3: with (B \in Boolean) { if(B = TRUE) call Update(self); };
         
         s4: if(Acl_PermissionType[self][Resource] = NULL) { Define(self, Resource) }
         
             else if(Acl_Status[self][Resource] = NULL) { Request(self, Resource); }
         
             else if(Acl_Status[self][Resource] = REQUESTED) { Decide(self, Resource); }
             
             else if(Acl_Status[self][Resource] = ALLOWED)
             {
              either { Revoke(self, Resource); }
              or { Use(self, Resource); }
             };
             
         s5: with (rand \in Boolean)
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
\* BEGIN TRANSLATION (chksum(pcal) = "68482efa" /\ chksum(tla) = "b9184269")
\* Procedure variable ResourceList of procedure Update at line 77 col 14 changed to ResourceList_
CONSTANT defaultInitValue
VARIABLES Acl_Status, Acl_PermissionType, Acl_PermissionLevel, Consent, Grid, 
          pc, stack, p2, ResourceList_, app1, app2, ResourceList, Resource

vars == << Acl_Status, Acl_PermissionType, Acl_PermissionLevel, Consent, Grid, 
           pc, stack, p2, ResourceList_, app1, app2, ResourceList, Resource
        >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ Acl_Status = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Acl_PermissionType = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Acl_PermissionLevel = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Consent = [a \in Processes |-> [r \in Resources |-> FALSE]]
        /\ Grid = [a \in Processes |-> [a2 \in Processes |-> FALSE]]
        (* Procedure Update *)
        /\ p2 = [ self \in ProcSet |-> defaultInitValue]
        /\ ResourceList_ = [ self \in ProcSet |-> Resources]
        (* Procedure Delegate *)
        /\ app1 = [ self \in ProcSet |-> defaultInitValue]
        /\ app2 = [ self \in ProcSet |-> defaultInitValue]
        /\ ResourceList = [ self \in ProcSet |-> Resources]
        (* Process AcmNext *)
        /\ Resource = [self \in Processes |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "s0"]

UPDATE(self) == /\ pc[self] = "UPDATE"
                /\ IF ResourceList_[self] # {}
                      THEN /\ \E r \in ResourceList_[self]:
                                /\ IF Acl_PermissionLevel[p2[self]][r] = NORMAL
                                      THEN /\ Acl_PermissionLevel' = [Acl_PermissionLevel EXCEPT ![p2[self]][r] = DANGEROUS]
                                           /\ Consent' = [Consent EXCEPT ![p2[self]][r] = FALSE]
                                      ELSE /\ TRUE
                                           /\ UNCHANGED << Acl_PermissionLevel, 
                                                           Consent >>
                                /\ ResourceList_' = [ResourceList_ EXCEPT ![self] = ResourceList_[self] \ {r}]
                           /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
                           /\ UNCHANGED << stack, p2 >>
                      ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ ResourceList_' = [ResourceList_ EXCEPT ![self] = Head(stack[self]).ResourceList_]
                           /\ p2' = [p2 EXCEPT ![self] = Head(stack[self]).p2]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << Acl_PermissionLevel, Consent >>
                /\ UNCHANGED << Acl_Status, Acl_PermissionType, Grid, app1, 
                                app2, ResourceList, Resource >>

Update(self) == UPDATE(self)

DELEGATE(self) == /\ pc[self] = "DELEGATE"
                  /\ IF ResourceList[self] # {}
                        THEN /\ \E r \in ResourceList[self]:
                                  /\ IF Acl_PermissionType[app2[self]][r] # NULL /\ Acl_PermissionType[app1[self]][r] = NULL
                                        THEN /\ Acl_PermissionType' = [Acl_PermissionType EXCEPT ![app1[self]][r] = Acl_PermissionType[app2[self]][r]]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED Acl_PermissionType
                                  /\ IF Acl_Status[app2[self]][r] # NULL /\ Acl_Status[app1[self]][r] = NULL
                                        THEN /\ Acl_Status' = [Acl_Status EXCEPT ![app1[self]][r] = Acl_Status[app2[self]][r]]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED Acl_Status
                                  /\ ResourceList' = [ResourceList EXCEPT ![self] = ResourceList[self] \ {r}]
                             /\ pc' = [pc EXCEPT ![self] = "DELEGATE"]
                             /\ UNCHANGED << stack, app1, app2 >>
                        ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ ResourceList' = [ResourceList EXCEPT ![self] = Head(stack[self]).ResourceList]
                             /\ app1' = [app1 EXCEPT ![self] = Head(stack[self]).app1]
                             /\ app2' = [app2 EXCEPT ![self] = Head(stack[self]).app2]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << Acl_Status, Acl_PermissionType >>
                  /\ UNCHANGED << Acl_PermissionLevel, Consent, Grid, p2, 
                                  ResourceList_, Resource >>

Delegate(self) == DELEGATE(self)

s0(self) == /\ pc[self] = "s0"
            /\ Grid' = [Grid EXCEPT ![self][self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, stack, p2, 
                            ResourceList_, app1, app2, ResourceList, Resource >>

s1(self) == /\ pc[self] = "s1"
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Grid, stack, p2, 
                            ResourceList_, app1, app2, ResourceList, Resource >>

s2(self) == /\ pc[self] = "s2"
            /\ \E R \in Resources:
                 Resource' = [Resource EXCEPT ![self] = R]
            /\ pc' = [pc EXCEPT ![self] = "s3"]
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Grid, stack, p2, 
                            ResourceList_, app1, app2, ResourceList >>

s3(self) == /\ pc[self] = "s3"
            /\ \E B \in Boolean:
                 IF B = TRUE
                    THEN /\ /\ p2' = [p2 EXCEPT ![self] = self]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Update",
                                                                     pc        |->  "s4",
                                                                     ResourceList_ |->  ResourceList_[self],
                                                                     p2        |->  p2[self] ] >>
                                                                 \o stack[self]]
                         /\ ResourceList_' = [ResourceList_ EXCEPT ![self] = Resources]
                         /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "s4"]
                         /\ UNCHANGED << stack, p2, ResourceList_ >>
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Grid, app1, app2, 
                            ResourceList, Resource >>

s4(self) == /\ pc[self] = "s4"
            /\ IF Acl_PermissionType[self][Resource[self]] = NULL
                  THEN /\ \E t \in PermissionTypes:
                            Acl_PermissionType' = [Acl_PermissionType EXCEPT ![self][Resource[self]] = t]
                       /\ Acl_PermissionLevel' = [Acl_PermissionLevel EXCEPT ![self][Resource[self]] = NORMAL]
                       /\ UNCHANGED << Acl_Status, Consent >>
                  ELSE /\ IF Acl_Status[self][Resource[self]] = NULL
                             THEN /\ Acl_Status' = [Acl_Status EXCEPT ![self][Resource[self]] = REQUESTED]
                                  /\ UNCHANGED Consent
                             ELSE /\ IF Acl_Status[self][Resource[self]] = REQUESTED
                                        THEN /\ \E b \in Boolean:
                                                  IF b = TRUE
                                                     THEN /\ Acl_Status' = [Acl_Status EXCEPT ![self][Resource[self]] = ALLOWED]
                                                          /\ Consent' = [Consent EXCEPT ![self][Resource[self]] = TRUE]
                                                     ELSE /\ Acl_Status' = [Acl_Status EXCEPT ![self][Resource[self]] = REJECTED]
                                                          /\ Consent' = [Consent EXCEPT ![self][Resource[self]] = FALSE]
                                        ELSE /\ IF Acl_Status[self][Resource[self]] = ALLOWED
                                                   THEN /\ \/ /\ Acl_Status' = [Acl_Status EXCEPT ![self][Resource[self]] = NULL]
                                                              /\ Consent' = [Consent EXCEPT ![self][Resource[self]] = FALSE]
                                                           \/ /\ Acl_Status' = [Acl_Status EXCEPT ![self][Resource[self]] = IN_USE]
                                                              /\ UNCHANGED Consent
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << Acl_Status, 
                                                                        Consent >>
                       /\ UNCHANGED << Acl_PermissionType, Acl_PermissionLevel >>
            /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << Grid, stack, p2, ResourceList_, app1, app2, 
                            ResourceList, Resource >>

s5(self) == /\ pc[self] = "s5"
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
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, p2, ResourceList_, 
                            Resource >>

AcmNext(self) == s0(self) \/ s1(self) \/ s2(self) \/ s3(self) \/ s4(self)
                    \/ s5(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Update(self) \/ Delegate(self))
           \/ (\E self \in Processes: AcmNext(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(AcmNext(self)) /\ WF_vars(Update(self)) /\ WF_vars(Delegate(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

AcmTypeOK == /\ Acl_Status \in [Processes -> [Resources -> ResourceStatus \cup {NULL}]]
             /\ Acl_PermissionType \in [Processes -> [Resources -> PermissionTypes \cup {NULL}]]
             /\ Acl_PermissionLevel \in [Processes -> [Resources -> PermissionLevels \cup {NULL}]]
             /\ Consent \in [Processes -> [Resources -> Boolean]]
             /\ Grid \in [Processes -> [Processes -> Boolean]]


AcmRedelegation == ~(\E p \in Processes:
                   \E r \in Resources:
                      /\ Acl_Status[p][r] = IN_USE
                      /\ Consent[p][r] # TRUE)

AcmLiveness == <> (\E p \in Processes:
                   \E r \in Resources:
                      Acl_Status[p][r] = ALLOWED \/ Acl_Status[p][r] = REJECTED)

=============================================================================
\* Modification History
\* Last modified Sat Jun 10 23:11:47 GMT+03:30 2023 by Amirhosein
\* Created Thu Mar 23 07:45:26 GMT+03:30 2023 by Amirhosein
