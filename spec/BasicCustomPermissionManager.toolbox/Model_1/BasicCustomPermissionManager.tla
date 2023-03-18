-------------------- MODULE BasicCustomPermissionManager --------------------
EXTENDS Naturals, Sequences

CONSTANTS A

ASSUME A \in Nat

Applications == 1..A

GRANT == "GRANT"
DENY == "DENY"
NULL == "NULL"
ALLOW == "ALLOW"
REJECT == "REJECT"
NORMAL == "NORMAL"
SENSITIVE == "SENSITIVE"

PermissionRequestDecision == { GRANT, DENY, NULL }
CustomPermission == { NORMAL, SENSITIVE, NULL }
UserConsent == { ALLOW, REJECT, NULL }
Boolean == { TRUE, FALSE }

(***       this is a comment containing the PlusCal code *

--algorithm PermissionManager
{
    variables appPerms = [i \in Applications |-> NULL];
              appCP = [i \in Applications |-> NULL];
              userConsent = [i \in Applications |-> NULL];
              installed = [p \in Applications |-> FALSE];
    
    macro installApp(app) { installed[app] := TRUE; }
    
    macro defineCP(app) { either { appCP[app] := NORMAL; }
                          or { appCP[app] := SENSITIVE; }}

    macro askUser(app) { either { appPerms[app] := GRANT; userConsent[app] := ALLOW; }
                            or { appPerms[app] := DENY; userConsent[app] := REJECT; }}
               
    macro updateApp(app) { if(appCP[app] = NULL) { defineCP(app); }
                           else { appCP[app] := NULL; }}
               
    procedure ask(app)
    {
        l1: if(appPerms[app] = GRANT) { return; }

            else if(appPerms[app] = DENY) { return; }

            else
            {
                if(appCP[app] = NORMAL) { appPerms[app] := GRANT; };
                else askUser(app);
                
                return;
            }
    }
    
    fair process (a \in Applications)
    {
        install: installApp(self);
        platform:- while (TRUE)
                   {
                        either { updateApp(self); }
                        or { either { if(appCP[self] = NULL) { defineCP(self); }}
                             or { call ask(self); }}
                   };
    }
}

    this ends the comment containing the PlusCal code
*************)             
\* BEGIN TRANSLATION (chksum(pcal) = "7e9be6d" /\ chksum(tla) = "e132a525")
CONSTANT defaultInitValue
VARIABLES appPerms, appCP, userConsent, installed, pc, stack, app

vars == << appPerms, appCP, userConsent, installed, pc, stack, app >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ appPerms = [i \in Applications |-> NULL]
        /\ appCP = [i \in Applications |-> NULL]
        /\ userConsent = [i \in Applications |-> NULL]
        /\ installed = [p \in Applications |-> FALSE]
        (* Procedure ask *)
        /\ app = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "install"]

l1(self) == /\ pc[self] = "l1"
            /\ IF appPerms[app[self]] = GRANT
                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << appPerms, userConsent >>
                  ELSE /\ IF appPerms[app[self]] = DENY
                             THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << appPerms, userConsent >>
                             ELSE /\ IF appCP[app[self]] = NORMAL
                                        THEN /\ appPerms' = [appPerms EXCEPT ![app[self]] = GRANT]
                                             /\ UNCHANGED userConsent
                                        ELSE /\ \/ /\ appPerms' = [appPerms EXCEPT ![app[self]] = GRANT]
                                                   /\ userConsent' = [userConsent EXCEPT ![app[self]] = ALLOW]
                                                \/ /\ appPerms' = [appPerms EXCEPT ![app[self]] = DENY]
                                                   /\ userConsent' = [userConsent EXCEPT ![app[self]] = REJECT]
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << appCP, installed >>

ask(self) == l1(self)

install(self) == /\ pc[self] = "install"
                 /\ installed' = [installed EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "platform"]
                 /\ UNCHANGED << appPerms, appCP, userConsent, stack, app >>

platform(self) == /\ pc[self] = "platform"
                  /\ \/ /\ IF appCP[self] = NULL
                              THEN /\ \/ /\ appCP' = [appCP EXCEPT ![self] = NORMAL]
                                      \/ /\ appCP' = [appCP EXCEPT ![self] = SENSITIVE]
                              ELSE /\ appCP' = [appCP EXCEPT ![self] = NULL]
                        /\ pc' = [pc EXCEPT ![self] = "platform"]
                        /\ UNCHANGED <<stack, app>>
                     \/ /\ \/ /\ IF appCP[self] = NULL
                                    THEN /\ \/ /\ appCP' = [appCP EXCEPT ![self] = NORMAL]
                                            \/ /\ appCP' = [appCP EXCEPT ![self] = SENSITIVE]
                                    ELSE /\ TRUE
                                         /\ appCP' = appCP
                              /\ pc' = [pc EXCEPT ![self] = "platform"]
                              /\ UNCHANGED <<stack, app>>
                           \/ /\ /\ app' = [app EXCEPT ![self] = self]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ask",
                                                                          pc        |->  "platform",
                                                                          app       |->  app[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "l1"]
                              /\ appCP' = appCP
                  /\ UNCHANGED << appPerms, userConsent, installed >>

a(self) == install(self) \/ platform(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: ask(self))
           \/ (\E self \in Applications: a(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : WF_vars((pc[self] # "platform") /\ a(self)) /\ WF_vars(ask(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK == /\ appPerms \in [Applications -> PermissionRequestDecision]
          /\ appCP \in [Applications -> CustomPermission]
          /\ userConsent \in [Applications -> UserConsent]
          /\ installed \in [Applications -> Boolean]

UserAgreed == [] ~(/\ \E m \in Applications : appCP[m] = SENSITIVE
                      /\ appPerms[m] = GRANT
                      /\ userConsent[m] # ALLOW)

=============================================================================
\* Modification History
\* Last modified Fri Mar 03 13:03:19 IRST 2023 by Amirhosein
