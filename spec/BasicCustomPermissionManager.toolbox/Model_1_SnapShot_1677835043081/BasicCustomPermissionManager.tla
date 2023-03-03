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
              appCP = [a \in Applications |-> NULL];
              userConsent = [a \in Applications |-> NULL];
              installed = [p \in Applications |-> FALSE];
    
    macro installApp(app) { installed[app] := TRUE; }
    
    macro defineCP(app) { either { appCP[app] := NORMAL; }
                          or { appCP[app] := SENSITIVE; }}
               
    macro askUser(a1, a2) { either { appPerms[a1] := GRANT; userConsent[a1] := ALLOW; }
                            or { appPerms[a1] := DENY; userConsent[a1] := REJECT; }}
               
    macro updateApp(app) { if(appCP[app] = NULL) { defineCP(app); }
                           else { appCP[app] := NULL; }}
               
    procedure ask(a1, a2)
    {
        l1: if(appPerms[a1] = GRANT) { return; }

            else if(appPerms[a1] = DENY) { return; }

            else
            {
                if(appCP[a2] = NORMAL) { appPerms[a1] := GRANT; };
                else askUser(a1, a2);
                
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
                             or { with (application \in (Applications \ {self})) { call ask(self, application); }}}
                   };
    }
}

    this ends the comment containing the PlusCal code
*************)             
\* BEGIN TRANSLATION (chksum(pcal) = "e58536e0" /\ chksum(tla) = "d2266c8c")
CONSTANT defaultInitValue
VARIABLES appPerms, appCP, userConsent, installed, pc, stack, a1, a2

vars == << appPerms, appCP, userConsent, installed, pc, stack, a1, a2 >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ appPerms = [i \in Applications |-> NULL]
        /\ appCP = [a \in Applications |-> NULL]
        /\ userConsent = [a \in Applications |-> NULL]
        /\ installed = [p \in Applications |-> FALSE]
        (* Procedure ask *)
        /\ a1 = [ self \in ProcSet |-> defaultInitValue]
        /\ a2 = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "install"]

l1(self) == /\ pc[self] = "l1"
            /\ IF appPerms[a1[self]] = GRANT
                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ a1' = [a1 EXCEPT ![self] = Head(stack[self]).a1]
                       /\ a2' = [a2 EXCEPT ![self] = Head(stack[self]).a2]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << appPerms, userConsent >>
                  ELSE /\ IF appPerms[a1[self]] = DENY
                             THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ a1' = [a1 EXCEPT ![self] = Head(stack[self]).a1]
                                  /\ a2' = [a2 EXCEPT ![self] = Head(stack[self]).a2]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << appPerms, userConsent >>
                             ELSE /\ IF appCP[a2[self]] = NORMAL
                                        THEN /\ appPerms' = [appPerms EXCEPT ![a1[self]] = GRANT]
                                             /\ UNCHANGED userConsent
                                        ELSE /\ \/ /\ appPerms' = [appPerms EXCEPT ![a1[self]] = GRANT]
                                                   /\ userConsent' = [userConsent EXCEPT ![a1[self]] = ALLOW]
                                                \/ /\ appPerms' = [appPerms EXCEPT ![a1[self]] = DENY]
                                                   /\ userConsent' = [userConsent EXCEPT ![a1[self]] = REJECT]
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ a1' = [a1 EXCEPT ![self] = Head(stack[self]).a1]
                                  /\ a2' = [a2 EXCEPT ![self] = Head(stack[self]).a2]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << appCP, installed >>

ask(self) == l1(self)

install(self) == /\ pc[self] = "install"
                 /\ installed' = [installed EXCEPT ![self] = TRUE]
                 /\ pc' = [pc EXCEPT ![self] = "platform"]
                 /\ UNCHANGED << appPerms, appCP, userConsent, stack, a1, a2 >>

platform(self) == /\ pc[self] = "platform"
                  /\ \/ /\ IF appCP[self] = NULL
                              THEN /\ \/ /\ appCP' = [appCP EXCEPT ![self] = NORMAL]
                                      \/ /\ appCP' = [appCP EXCEPT ![self] = SENSITIVE]
                              ELSE /\ appCP' = [appCP EXCEPT ![self] = NULL]
                        /\ pc' = [pc EXCEPT ![self] = "platform"]
                        /\ UNCHANGED <<stack, a1, a2>>
                     \/ /\ \/ /\ IF appCP[self] = NULL
                                    THEN /\ \/ /\ appCP' = [appCP EXCEPT ![self] = NORMAL]
                                            \/ /\ appCP' = [appCP EXCEPT ![self] = SENSITIVE]
                                    ELSE /\ TRUE
                                         /\ appCP' = appCP
                              /\ pc' = [pc EXCEPT ![self] = "platform"]
                              /\ UNCHANGED <<stack, a1, a2>>
                           \/ /\ \E application \in (Applications \ {self}):
                                   /\ /\ a1' = [a1 EXCEPT ![self] = self]
                                      /\ a2' = [a2 EXCEPT ![self] = application]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ask",
                                                                               pc        |->  "platform",
                                                                               a1        |->  a1[self],
                                                                               a2        |->  a2[self] ] >>
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
\* Last modified Fri Mar 03 12:47:17 IRST 2023 by Amirhosein
