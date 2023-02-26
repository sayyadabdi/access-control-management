------------ MODULE PermissionManager ------------
EXTENDS Naturals, Sequences

CONSTANTS P, A

ASSUME P \in Nat
ASSUME A \in Nat

Permissions == 1..P
Applications == 1..A

GRANT == "GRANT"
DENY == "DENY"
NULL == "NULL"
ALLOW == "ALLOW"
REJECT == "REJECT"

PermissionRequestDecision == { GRANT, DENY, NULL }
UserConsent == { ALLOW, REJECT, NULL }

(***       this is a comment containing the PlusCal code *

--algorithm PermissionManager
{
    variables appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]];
              permConsents = [p \in Permissions |-> [a \in Applications |-> NULL]];
              installed = [p \in Applications |-> FALSE]

    define { appInstalled(app) == installed[app] = TRUE };
    
    macro arbitraryDecision(app, perm) { either { appPerms[app][perm] := GRANT }
                                         or { appPerms[app][perm] := DENY } }
    macro askUserPermission(app, perm)
    {
        either
        {
            appPerms[app][perm] := GRANT;
            permConsents[perm][app] := ALLOW
        }
        or
        {
            appPerms[app][perm] := REJECT;
            permConsents[perm][app] := DENY;
        }
    }
    
    macro revokePermissions(app) { appPerms[app] := [i \in Permissions |-> NULL]; }
    
    procedure ask(app, perm) {l1: if(appPerms[app][perm] = GRANT) { skip; }; return}
    procedure installApp(app) {l2: installed[app] := TRUE; return}
    procedure uninstallApp(app) {l3: revokePermissions(app); installed[app] := FALSE; return}
    procedure makeDecision(app, perm)
    {
        l4: either { call ask(app, perm); return }
            or { arbitraryDecision(app, perm); return};
    }

    fair process (a \in Applications)
    {
        platform:- while (TRUE)
                   {
                        either { if(~appInstalled(app)) { call installApp(self); } }
                        or
                        {
                            if(appInstalled(app))
                            {
                                either { call uninstallApp(self); }
                                or { with (p \in Permissions) { call ask(self, p); } }
                            }
                        };
                   };
    }
}

    this ends the comment containing the PlusCal code
*************)             
\* BEGIN TRANSLATION (chksum(pcal) = "513abff1" /\ chksum(tla) = "93dbf3e")
\* Parameter app of procedure ask at line 49 col 19 changed to app_
\* Parameter perm of procedure ask at line 49 col 24 changed to perm_
\* Parameter app of procedure installApp at line 50 col 26 changed to app_i
\* Parameter app of procedure uninstallApp at line 51 col 28 changed to app_u
CONSTANT defaultInitValue
VARIABLES appPerms, permConsents, installed, pc, stack

(* define statement *)
appInstalled(app) == installed[app] = TRUE

VARIABLES app_, perm_, app_i, app_u, app, perm

vars == << appPerms, permConsents, installed, pc, stack, app_, perm_, app_i, 
           app_u, app, perm >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]]
        /\ permConsents = [p \in Permissions |-> [a \in Applications |-> NULL]]
        /\ installed = [p \in Applications |-> FALSE]
        (* Procedure ask *)
        /\ app_ = [ self \in ProcSet |-> defaultInitValue]
        /\ perm_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure installApp *)
        /\ app_i = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure uninstallApp *)
        /\ app_u = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure makeDecision *)
        /\ app = [ self \in ProcSet |-> defaultInitValue]
        /\ perm = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "platform"]

l1(self) == /\ pc[self] = "l1"
            /\ IF appPerms[app_[self]][perm_[self]] = GRANT
                  THEN /\ TRUE
                  ELSE /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
            /\ perm_' = [perm_ EXCEPT ![self] = Head(stack[self]).perm_]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << appPerms, permConsents, installed, app_i, app_u, 
                            app, perm >>

ask(self) == l1(self)

l2(self) == /\ pc[self] = "l2"
            /\ installed' = [installed EXCEPT ![app_i[self]] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ app_i' = [app_i EXCEPT ![self] = Head(stack[self]).app_i]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << appPerms, permConsents, app_, perm_, app_u, app, 
                            perm >>

installApp(self) == l2(self)

l3(self) == /\ pc[self] = "l3"
            /\ appPerms' = [appPerms EXCEPT ![app_u[self]] = [i \in Permissions |-> NULL]]
            /\ installed' = [installed EXCEPT ![app_u[self]] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ app_u' = [app_u EXCEPT ![self] = Head(stack[self]).app_u]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << permConsents, app_, perm_, app_i, app, perm >>

uninstallApp(self) == l3(self)

l4(self) == /\ pc[self] = "l4"
            /\ \/ /\ /\ app_' = [app_ EXCEPT ![self] = app[self]]
                     /\ perm_' = [perm_ EXCEPT ![self] = perm[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ask",
                                                              pc        |->  Head(stack[self]).pc,
                                                              app_      |->  app_[self],
                                                              perm_     |->  perm_[self] ] >>
                                                          \o Tail(stack[self])]
                  /\ pc' = [pc EXCEPT ![self] = "l1"]
                  /\ UNCHANGED <<appPerms, app, perm>>
               \/ /\ \/ /\ appPerms' = [appPerms EXCEPT ![app[self]][perm[self]] = GRANT]
                     \/ /\ appPerms' = [appPerms EXCEPT ![app[self]][perm[self]] = DENY]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                  /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED <<app_, perm_>>
            /\ UNCHANGED << permConsents, installed, app_i, app_u >>

makeDecision(self) == l4(self)

platform(self) == /\ pc[self] = "platform"
                  /\ \/ /\ IF ~appInstalled(app[self])
                              THEN /\ /\ app_i' = [app_i EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "installApp",
                                                                               pc        |->  "platform",
                                                                               app_i     |->  app_i[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "l2"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "platform"]
                                   /\ UNCHANGED << stack, app_i >>
                        /\ UNCHANGED <<app_, perm_, app_u>>
                     \/ /\ IF appInstalled(app[self])
                              THEN /\ \/ /\ /\ app_u' = [app_u EXCEPT ![self] = self]
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                                     pc        |->  "platform",
                                                                                     app_u     |->  app_u[self] ] >>
                                                                                 \o stack[self]]
                                         /\ pc' = [pc EXCEPT ![self] = "l3"]
                                         /\ UNCHANGED <<app_, perm_>>
                                      \/ /\ \E p \in Permissions:
                                              /\ /\ app_' = [app_ EXCEPT ![self] = self]
                                                 /\ perm_' = [perm_ EXCEPT ![self] = p]
                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ask",
                                                                                          pc        |->  "platform",
                                                                                          app_      |->  app_[self],
                                                                                          perm_     |->  perm_[self] ] >>
                                                                                      \o stack[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "l1"]
                                         /\ app_u' = app_u
                              ELSE /\ pc' = [pc EXCEPT ![self] = "platform"]
                                   /\ UNCHANGED << stack, app_, perm_, app_u >>
                        /\ app_i' = app_i
                  /\ UNCHANGED << appPerms, permConsents, installed, app, perm >>

a(self) == platform(self)

Next == (\E self \in ProcSet:  \/ ask(self) \/ installApp(self)
                               \/ uninstallApp(self) \/ makeDecision(self))
           \/ (\E self \in Applications: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : /\ WF_vars((pc[self] # "platform") /\ a(self))
                                      /\ WF_vars(installApp(self))
                                      /\ WF_vars(uninstallApp(self))
                                      /\ WF_vars(ask(self))

\* END TRANSLATION

TypeOK == /\ appPerms \in [Applications -> [Permissions -> PermissionRequestDecision]]

=============================================================================
\* Modification History
\* Last modified Sun Feb 26 22:06:11 IRST 2023 by Amirhosein
