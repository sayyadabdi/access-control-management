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
OTP == "OTP"

NORMAL == "NORMAL"
SIGNATURE == "SIGNATURE"
DANGEROUS == "DANGEROUS"

NOT_INSTALLED == "NOT_INSTALLED"
STOPPED == "STOPPED"
RUNNING == "RUNNING"
PAUSED == "PAUSED"

Boolean == { TRUE, FALSE }
ResourceStatus == { REQUESTED, ALLOWED, REJECTED, IN_USE }
PermissionTypes == { URI_PERMISSION, CUSTOM_PERMISSION, OTP }
PermissionLevels == { NORMAL, SIGNATURE, DANGEROUS }
ProcessStates == { NOT_INSTALLED, STOPPED, RUNNING, PAUSED }

(***--algorithm AccessControlManagement
{
    variables
     Acl_Status = [a \in Processes |-> [r \in Resources |-> NULL]];
     Acl_PermissionType = [a \in Processes |-> [r \in Resources |-> NULL]];
     Acl_PermissionLevel = [a \in Processes |-> [r \in Resources |-> NULL]];
     Consent = [a \in Processes |-> [r \in Resources |-> FALSE]];
     Grid = [a \in Processes |-> [a2 \in Processes |-> FALSE]];
     Clock = [a \in Processes |-> 0];
     ProcessState = [a \in Processes |-> NOT_INSTALLED];
     PauseHistory = [a \in Processes |-> FALSE];

    macro Define(p, r)
    {
     with(t \in PermissionTypes)
     { Acl_PermissionType[p][r] := t; };
     with(t \in PermissionLevels)
     { Acl_PermissionLevel[p][r] := t; };
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
       if(Acl_PermissionLevel[p2][r] # NULL)
       {
        with(l \in PermissionLevels)
        {
         Acl_PermissionLevel[p2][r] := l;
         Consent[p2][r] := FALSE;
        }
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
       if(/\ Acl_PermissionType[app2][r] # NULL
          /\ Acl_PermissionType[app1][r] = NULL)
        Acl_PermissionType[app1][r] := Acl_PermissionType[app2][r];
       
       if(Acl_Status[app2][r] # NULL /\ Acl_Status[app1][r] = NULL)
        Acl_Status[app1][r] := Acl_Status[app2][r];
        
       ResourceList := ResourceList \ {r};
      }
     };
     return;
    }
    
    procedure ClearOtp(app)
    variable ResourceList = Resources;
    {     
     CLEAR_OTP:
     while(ResourceList # {})
     {
      with(r \in ResourceList)
      {
       if(Acl_PermissionType[app][r] = OTP)
       {
        Acl_Status[app][r] := NULL;
        Consent[app][r] := FALSE;
       };
       
       ResourceList := ResourceList \ {r};
      }
     };
     
     RESET_CLOCK: Clock[app] := 0;
     return;
    }

    fair process (AcmNext \in Processes)
    variable Resource
    {
        s0: ProcessState[self] := STOPPED;
        
        s10: ProcessState[self] := RUNNING;
        
        s1: Grid[self][self] := TRUE;
        
        s2: while(TRUE)
        {
         s51: if(ProcessState[self] = PAUSED)
         {
          either
          {
           if(\E r \in Resources : /\ Acl_PermissionType[self][r] = OTP
                                   /\ (\/ Acl_Status[self][r] = ALLOWED
                                       \/ Acl_Status[self][r] = IN_USE))
           {
            call ClearOtp(self);
           };

           STOPPING_APP: ProcessState[self] := STOPPED;
          }
          or
          {
           ProcessState[self] := RUNNING;
           if(Acl_PermissionType[self][Resource] = OTP
                     /\ Acl_Status[self][Resource] = IN_USE
                     /\ Clock[self] < 3)
                  {
                   Clock[self] := Clock[self] + 1;
                  }
          }
         };
        
         s50: if(ProcessState[self] # RUNNING)
               goto s2;
         
         s3: with (R \in Resources) { Resource := R; };
         
         s4: with (B \in Boolean) { if(B = TRUE) call Update(self); };
         
         s5: if(Acl_PermissionType[self][Resource] = NULL)
              {
               Define(self, Resource)
              }
         
             else if(Acl_Status[self][Resource] = NULL)
             {
              Request(self, Resource);
             }
         
             else if(Acl_Status[self][Resource] = REQUESTED)
             {
              Decide(self, Resource);
             }
             
             else if(Acl_Status[self][Resource] = ALLOWED)
             {
              either { Revoke(self, Resource); }
              or { Use(self, Resource); }
             };

         s6: with (rand \in Boolean)
         {
         if(rand = TRUE)
         {
          with (a \in (Processes \ {self}))
          {
           Connect(self, a);
           call Delegate(self, a);
          }
         }
         };
         
         s7: with (rand \in Boolean)
         {
          if(rand = TRUE)
         {
           if(ProcessState[self] = RUNNING)
           {
            ProcessState[self] := PAUSED;
            PauseHistory[self] := TRUE;
           }
          }
         }
        }
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "c5aa8986" /\ chksum(tla) = "9c05861f")
\* Procedure variable ResourceList of procedure Update at line 90 col 14 changed to ResourceList_
\* Procedure variable ResourceList of procedure Delegate at line 113 col 14 changed to ResourceList_D
CONSTANT defaultInitValue
VARIABLES Acl_Status, Acl_PermissionType, Acl_PermissionLevel, Consent, Grid, 
          Clock, ProcessState, PauseHistory, pc, stack, p2, ResourceList_, 
          app1, app2, ResourceList_D, app, ResourceList, Resource

vars == << Acl_Status, Acl_PermissionType, Acl_PermissionLevel, Consent, Grid, 
           Clock, ProcessState, PauseHistory, pc, stack, p2, ResourceList_, 
           app1, app2, ResourceList_D, app, ResourceList, Resource >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ Acl_Status = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Acl_PermissionType = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Acl_PermissionLevel = [a \in Processes |-> [r \in Resources |-> NULL]]
        /\ Consent = [a \in Processes |-> [r \in Resources |-> FALSE]]
        /\ Grid = [a \in Processes |-> [a2 \in Processes |-> FALSE]]
        /\ Clock = [a \in Processes |-> 0]
        /\ ProcessState = [a \in Processes |-> NOT_INSTALLED]
        /\ PauseHistory = [a \in Processes |-> FALSE]
        (* Procedure Update *)
        /\ p2 = [ self \in ProcSet |-> defaultInitValue]
        /\ ResourceList_ = [ self \in ProcSet |-> Resources]
        (* Procedure Delegate *)
        /\ app1 = [ self \in ProcSet |-> defaultInitValue]
        /\ app2 = [ self \in ProcSet |-> defaultInitValue]
        /\ ResourceList_D = [ self \in ProcSet |-> Resources]
        (* Procedure ClearOtp *)
        /\ app = [ self \in ProcSet |-> defaultInitValue]
        /\ ResourceList = [ self \in ProcSet |-> Resources]
        (* Process AcmNext *)
        /\ Resource = [self \in Processes |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "s0"]

UPDATE(self) == /\ pc[self] = "UPDATE"
                /\ IF ResourceList_[self] # {}
                      THEN /\ \E r \in ResourceList_[self]:
                                /\ IF Acl_PermissionLevel[p2[self]][r] # NULL
                                      THEN /\ \E l \in PermissionLevels:
                                                /\ Acl_PermissionLevel' = [Acl_PermissionLevel EXCEPT ![p2[self]][r] = l]
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
                /\ UNCHANGED << Acl_Status, Acl_PermissionType, Grid, Clock, 
                                ProcessState, PauseHistory, app1, app2, 
                                ResourceList_D, app, ResourceList, Resource >>

Update(self) == UPDATE(self)

DELEGATE(self) == /\ pc[self] = "DELEGATE"
                  /\ IF ResourceList_D[self] # {}
                        THEN /\ \E r \in ResourceList_D[self]:
                                  /\ IF /\ Acl_PermissionType[app2[self]][r] # NULL
                                        /\ Acl_PermissionType[app1[self]][r] = NULL
                                        THEN /\ Acl_PermissionType' = [Acl_PermissionType EXCEPT ![app1[self]][r] = Acl_PermissionType[app2[self]][r]]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED Acl_PermissionType
                                  /\ IF Acl_Status[app2[self]][r] # NULL /\ Acl_Status[app1[self]][r] = NULL
                                        THEN /\ Acl_Status' = [Acl_Status EXCEPT ![app1[self]][r] = Acl_Status[app2[self]][r]]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED Acl_Status
                                  /\ ResourceList_D' = [ResourceList_D EXCEPT ![self] = ResourceList_D[self] \ {r}]
                             /\ pc' = [pc EXCEPT ![self] = "DELEGATE"]
                             /\ UNCHANGED << stack, app1, app2 >>
                        ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ ResourceList_D' = [ResourceList_D EXCEPT ![self] = Head(stack[self]).ResourceList_D]
                             /\ app1' = [app1 EXCEPT ![self] = Head(stack[self]).app1]
                             /\ app2' = [app2 EXCEPT ![self] = Head(stack[self]).app2]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             /\ UNCHANGED << Acl_Status, Acl_PermissionType >>
                  /\ UNCHANGED << Acl_PermissionLevel, Consent, Grid, Clock, 
                                  ProcessState, PauseHistory, p2, 
                                  ResourceList_, app, ResourceList, Resource >>

Delegate(self) == DELEGATE(self)

CLEAR_OTP(self) == /\ pc[self] = "CLEAR_OTP"
                   /\ IF ResourceList[self] # {}
                         THEN /\ \E r \in ResourceList[self]:
                                   /\ IF Acl_PermissionType[app[self]][r] = OTP
                                         THEN /\ Acl_Status' = [Acl_Status EXCEPT ![app[self]][r] = NULL]
                                              /\ Consent' = [Consent EXCEPT ![app[self]][r] = FALSE]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << Acl_Status, 
                                                              Consent >>
                                   /\ ResourceList' = [ResourceList EXCEPT ![self] = ResourceList[self] \ {r}]
                              /\ pc' = [pc EXCEPT ![self] = "CLEAR_OTP"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "RESET_CLOCK"]
                              /\ UNCHANGED << Acl_Status, Consent, 
                                              ResourceList >>
                   /\ UNCHANGED << Acl_PermissionType, Acl_PermissionLevel, 
                                   Grid, Clock, ProcessState, PauseHistory, 
                                   stack, p2, ResourceList_, app1, app2, 
                                   ResourceList_D, app, Resource >>

RESET_CLOCK(self) == /\ pc[self] = "RESET_CLOCK"
                     /\ Clock' = [Clock EXCEPT ![app[self]] = 0]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ ResourceList' = [ResourceList EXCEPT ![self] = Head(stack[self]).ResourceList]
                     /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                                     Acl_PermissionLevel, Consent, Grid, 
                                     ProcessState, PauseHistory, p2, 
                                     ResourceList_, app1, app2, ResourceList_D, 
                                     Resource >>

ClearOtp(self) == CLEAR_OTP(self) \/ RESET_CLOCK(self)

s0(self) == /\ pc[self] = "s0"
            /\ ProcessState' = [ProcessState EXCEPT ![self] = STOPPED]
            /\ pc' = [pc EXCEPT ![self] = "s10"]
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Grid, Clock, 
                            PauseHistory, stack, p2, ResourceList_, app1, app2, 
                            ResourceList_D, app, ResourceList, Resource >>

s10(self) == /\ pc[self] = "s10"
             /\ ProcessState' = [ProcessState EXCEPT ![self] = RUNNING]
             /\ pc' = [pc EXCEPT ![self] = "s1"]
             /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                             Acl_PermissionLevel, Consent, Grid, Clock, 
                             PauseHistory, stack, p2, ResourceList_, app1, 
                             app2, ResourceList_D, app, ResourceList, Resource >>

s1(self) == /\ pc[self] = "s1"
            /\ Grid' = [Grid EXCEPT ![self][self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Clock, ProcessState, 
                            PauseHistory, stack, p2, ResourceList_, app1, app2, 
                            ResourceList_D, app, ResourceList, Resource >>

s2(self) == /\ pc[self] = "s2"
            /\ pc' = [pc EXCEPT ![self] = "s51"]
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Grid, Clock, 
                            ProcessState, PauseHistory, stack, p2, 
                            ResourceList_, app1, app2, ResourceList_D, app, 
                            ResourceList, Resource >>

s51(self) == /\ pc[self] = "s51"
             /\ IF ProcessState[self] = PAUSED
                   THEN /\ \/ /\ IF \E r \in Resources : /\ Acl_PermissionType[self][r] = OTP
                                                         /\ (\/ Acl_Status[self][r] = ALLOWED
                                                             \/ Acl_Status[self][r] = IN_USE)
                                    THEN /\ /\ app' = [app EXCEPT ![self] = self]
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ClearOtp",
                                                                                     pc        |->  "STOPPING_APP",
                                                                                     ResourceList |->  ResourceList[self],
                                                                                     app       |->  app[self] ] >>
                                                                                 \o stack[self]]
                                         /\ ResourceList' = [ResourceList EXCEPT ![self] = Resources]
                                         /\ pc' = [pc EXCEPT ![self] = "CLEAR_OTP"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "STOPPING_APP"]
                                         /\ UNCHANGED << stack, app, 
                                                         ResourceList >>
                              /\ UNCHANGED <<Clock, ProcessState>>
                           \/ /\ ProcessState' = [ProcessState EXCEPT ![self] = RUNNING]
                              /\ IF Acl_PermissionType[self][Resource[self]] = OTP
                                           /\ Acl_Status[self][Resource[self]] = IN_USE
                                           /\ Clock[self] < 3
                                    THEN /\ Clock' = [Clock EXCEPT ![self] = Clock[self] + 1]
                                    ELSE /\ TRUE
                                         /\ Clock' = Clock
                              /\ pc' = [pc EXCEPT ![self] = "s50"]
                              /\ UNCHANGED <<stack, app, ResourceList>>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s50"]
                        /\ UNCHANGED << Clock, ProcessState, stack, app, 
                                        ResourceList >>
             /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                             Acl_PermissionLevel, Consent, Grid, PauseHistory, 
                             p2, ResourceList_, app1, app2, ResourceList_D, 
                             Resource >>

STOPPING_APP(self) == /\ pc[self] = "STOPPING_APP"
                      /\ ProcessState' = [ProcessState EXCEPT ![self] = STOPPED]
                      /\ pc' = [pc EXCEPT ![self] = "s50"]
                      /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                                      Acl_PermissionLevel, Consent, Grid, 
                                      Clock, PauseHistory, stack, p2, 
                                      ResourceList_, app1, app2, 
                                      ResourceList_D, app, ResourceList, 
                                      Resource >>

s50(self) == /\ pc[self] = "s50"
             /\ IF ProcessState[self] # RUNNING
                   THEN /\ pc' = [pc EXCEPT ![self] = "s2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "s3"]
             /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                             Acl_PermissionLevel, Consent, Grid, Clock, 
                             ProcessState, PauseHistory, stack, p2, 
                             ResourceList_, app1, app2, ResourceList_D, app, 
                             ResourceList, Resource >>

s3(self) == /\ pc[self] = "s3"
            /\ \E R \in Resources:
                 Resource' = [Resource EXCEPT ![self] = R]
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Grid, Clock, 
                            ProcessState, PauseHistory, stack, p2, 
                            ResourceList_, app1, app2, ResourceList_D, app, 
                            ResourceList >>

s4(self) == /\ pc[self] = "s4"
            /\ \E B \in Boolean:
                 IF B = TRUE
                    THEN /\ /\ p2' = [p2 EXCEPT ![self] = self]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Update",
                                                                     pc        |->  "s5",
                                                                     ResourceList_ |->  ResourceList_[self],
                                                                     p2        |->  p2[self] ] >>
                                                                 \o stack[self]]
                         /\ ResourceList_' = [ResourceList_ EXCEPT ![self] = Resources]
                         /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "s5"]
                         /\ UNCHANGED << stack, p2, ResourceList_ >>
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Grid, Clock, 
                            ProcessState, PauseHistory, app1, app2, 
                            ResourceList_D, app, ResourceList, Resource >>

s5(self) == /\ pc[self] = "s5"
            /\ IF Acl_PermissionType[self][Resource[self]] = NULL
                  THEN /\ \E t \in PermissionTypes:
                            Acl_PermissionType' = [Acl_PermissionType EXCEPT ![self][Resource[self]] = t]
                       /\ \E t \in PermissionLevels:
                            Acl_PermissionLevel' = [Acl_PermissionLevel EXCEPT ![self][Resource[self]] = t]
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
            /\ pc' = [pc EXCEPT ![self] = "s6"]
            /\ UNCHANGED << Grid, Clock, ProcessState, PauseHistory, stack, p2, 
                            ResourceList_, app1, app2, ResourceList_D, app, 
                            ResourceList, Resource >>

s6(self) == /\ pc[self] = "s6"
            /\ \E rand \in Boolean:
                 IF rand = TRUE
                    THEN /\ \E a \in (Processes \ {self}):
                              /\ Grid' = [Grid EXCEPT ![self][a] = TRUE]
                              /\ /\ app1' = [app1 EXCEPT ![self] = self]
                                 /\ app2' = [app2 EXCEPT ![self] = a]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Delegate",
                                                                          pc        |->  "s7",
                                                                          ResourceList_D |->  ResourceList_D[self],
                                                                          app1      |->  app1[self],
                                                                          app2      |->  app2[self] ] >>
                                                                      \o stack[self]]
                              /\ ResourceList_D' = [ResourceList_D EXCEPT ![self] = Resources]
                              /\ pc' = [pc EXCEPT ![self] = "DELEGATE"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "s7"]
                         /\ UNCHANGED << Grid, stack, app1, app2, 
                                         ResourceList_D >>
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Clock, ProcessState, 
                            PauseHistory, p2, ResourceList_, app, ResourceList, 
                            Resource >>

s7(self) == /\ pc[self] = "s7"
            /\ \E rand \in Boolean:
                 IF rand = TRUE
                    THEN /\ IF ProcessState[self] = RUNNING
                               THEN /\ ProcessState' = [ProcessState EXCEPT ![self] = PAUSED]
                                    /\ PauseHistory' = [PauseHistory EXCEPT ![self] = TRUE]
                               ELSE /\ TRUE
                                    /\ UNCHANGED << ProcessState, PauseHistory >>
                    ELSE /\ TRUE
                         /\ UNCHANGED << ProcessState, PauseHistory >>
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << Acl_Status, Acl_PermissionType, 
                            Acl_PermissionLevel, Consent, Grid, Clock, stack, 
                            p2, ResourceList_, app1, app2, ResourceList_D, app, 
                            ResourceList, Resource >>

AcmNext(self) == s0(self) \/ s10(self) \/ s1(self) \/ s2(self) \/ s51(self)
                    \/ STOPPING_APP(self) \/ s50(self) \/ s3(self)
                    \/ s4(self) \/ s5(self) \/ s6(self) \/ s7(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ Update(self) \/ Delegate(self)
                               \/ ClearOtp(self))
           \/ (\E self \in Processes: AcmNext(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : /\ WF_vars(AcmNext(self))
                                   /\ WF_vars(ClearOtp(self))
                                   /\ WF_vars(Update(self))
                                   /\ WF_vars(Delegate(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

AcmTypeOK == /\ Acl_Status \in [Processes -> [Resources -> ResourceStatus \cup {NULL}]]
             /\ Acl_PermissionType \in [Processes -> [Resources -> PermissionTypes \cup {NULL}]]
             /\ Acl_PermissionLevel \in [Processes -> [Resources -> PermissionLevels \cup {NULL}]]
             /\ Consent \in [Processes -> [Resources -> Boolean]]
             /\ Grid \in [Processes -> [Processes -> Boolean]]
             /\ Clock \in [Processes -> Nat]
             /\ ProcessState \in [Processes -> ProcessStates]
             /\ PauseHistory \in [Processes -> Boolean]


AcmConsent == ~(\E p \in Processes:
                \E r \in Resources:
                   /\ Acl_Status[p][r] = IN_USE
                   /\ Consent[p][r] # TRUE)

AcmLiveness == <> (\E p \in Processes:
                   \E r \in Resources:
                      \/ Acl_Status[p][r] = ALLOWED
                      \/ Acl_Status[p][r] = REJECTED
                      \/ ProcessState[p] = STOPPED)

AcmOtpConsistent == (\A p \in Processes:
                      \/ Clock[p] < 2
                      \/ PauseHistory[p] = FALSE)

=============================================================================
\* Modification History
\* Last modified Fri Jun 16 19:29:41 GMT+03:30 2023 by Amirhosein
\* Created Thu Mar 23 07:45:26 GMT+03:30 2023 by Amirhosein
