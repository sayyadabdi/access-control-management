------------------------------ MODULE PManager ------------------------------
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
NORMAL == "NORMAL"
SENSITIVE == "SENSITIVE"

Boolean == { TRUE, FALSE }
UserConsent == { ALLOW, REJECT, NULL }
CustomPermission == { NORMAL, SENSITIVE, NULL }
PermissionRequestDecision == { GRANT, DENY, NULL }

(***       this is a comment containing the PlusCal code *
--algorithm PermissionManager
{
    variables appCP = [i \in Applications |-> NULL];
              installed = [p \in Applications |-> FALSE];
              appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]];
              permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]];              
              appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]];

    define { appInstalled(app) == installed[app] = TRUE };
    
    macro arbitraryDecision(app, perm) { either { appPerms[app][perm] := GRANT; appPermConsents[app][perm] := ALLOW; }
                                         or { appPerms[app][perm] := DENY; appPermConsents[app][perm] := REJECT; } }
                                         
    macro installApp(app) { installed[app] := TRUE; }
                                         
    macro defineCP(app) { either { appCP[app] := NORMAL; }
    or { appCP[app] := SENSITIVE; } }

    macro askUserPermission(app, perm) { either { appPerms[app][perm] := GRANT; appPermConsents[app][perm] := ALLOW; }
        or { appPerms[app][perm] := DENY; appPermConsents[app][perm] := REJECT; } }
    
    macro updateApp(app) { if(appCP[app] = NULL) { defineCP(app); }
                           else { appCP[app] := NULL; }}
    
    (*macro revokePermissions(app) { appPerms[app] := [i \in Permissions |-> NULL]; }*)
    
    procedure ask(app, perm) { l1: if(appPerms[app][perm] = GRANT) { permsInUse[app][perm] := TRUE; return }
                                   else if(appPerms[app][perm] = DENY) { permsInUse[app][perm] := FALSE; return }
                                   else { l2: call makeDecision(app, perm); l3: if(appPerms[app][perm] = GRANT) { permsInUse[app][perm] := TRUE; }; l4: return; } }
    
    procedure installApp(app) {l5: installed[app] := TRUE; return}
    procedure uninstallApp(app) { l6: installed[app] := FALSE; permsInUse[app] := [p \in Permissions |-> FALSE]; appPermConsents[app] := [p \in Permissions |-> NULL]; return; }
    procedure makeDecision(app, perm) { l7: either { askUserPermission(app, perm); return } 
                                            or { arbitraryDecision(app, perm); return}; }

    fair process (a \in Applications)
    {
        platform:- while (TRUE)
                   {
                    if(~appInstalled(self)) { call installApp(self); }
                    else
                    {
                        either { call uninstallApp(self); }
                        or
                        {
                            either { updateApp(self); }
                            or
                            {
                                either { if(appCP[self] = NULL) { defineCP(self); } }
                                or { with (p \in Permissions) { call ask(self, p); } }
                            }
                        }
                    }
                   };
    }
}

    this ends the comment containing the PlusCal code
*************)             
\* BEGIN TRANSLATION (chksum(pcal) = "c2a575ee" /\ chksum(tla) = "23a048b5")
\* Parameter app of procedure ask at line 52 col 19 changed to app_
\* Parameter perm of procedure ask at line 52 col 24 changed to perm_
\* Parameter app of procedure installApp at line 56 col 26 changed to app_i
\* Parameter app of procedure uninstallApp at line 57 col 28 changed to app_u
CONSTANT defaultInitValue
VARIABLES appCP, installed, appPerms, permsInUse, appPermConsents, pc, stack

(* define statement *)
appInstalled(app) == installed[app] = TRUE

VARIABLES app_, perm_, app_i, app_u, app, perm

vars == << appCP, installed, appPerms, permsInUse, appPermConsents, pc, stack, 
           app_, perm_, app_i, app_u, app, perm >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ appCP = [i \in Applications |-> NULL]
        /\ installed = [p \in Applications |-> FALSE]
        /\ appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]]
        /\ permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]]
        /\ appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]]
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
                  THEN /\ permsInUse' = [permsInUse EXCEPT ![app_[self]][perm_[self]] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
                       /\ perm_' = [perm_ EXCEPT ![self] = Head(stack[self]).perm_]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  ELSE /\ IF appPerms[app_[self]][perm_[self]] = DENY
                             THEN /\ permsInUse' = [permsInUse EXCEPT ![app_[self]][perm_[self]] = FALSE]
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
                                  /\ perm_' = [perm_ EXCEPT ![self] = Head(stack[self]).perm_]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "l2"]
                                  /\ UNCHANGED << permsInUse, stack, app_, 
                                                  perm_ >>
            /\ UNCHANGED << appCP, installed, appPerms, appPermConsents, app_i, 
                            app_u, app, perm >>

l2(self) == /\ pc[self] = "l2"
            /\ /\ app' = [app EXCEPT ![self] = app_[self]]
               /\ perm' = [perm EXCEPT ![self] = perm_[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "makeDecision",
                                                        pc        |->  "l3",
                                                        app       |->  app[self],
                                                        perm      |->  perm[self] ] >>
                                                    \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "l7"]
            /\ UNCHANGED << appCP, installed, appPerms, permsInUse, 
                            appPermConsents, app_, perm_, app_i, app_u >>

l3(self) == /\ pc[self] = "l3"
            /\ IF appPerms[app_[self]][perm_[self]] = GRANT
                  THEN /\ permsInUse' = [permsInUse EXCEPT ![app_[self]][perm_[self]] = TRUE]
                  ELSE /\ TRUE
                       /\ UNCHANGED permsInUse
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << appCP, installed, appPerms, appPermConsents, stack, 
                            app_, perm_, app_i, app_u, app, perm >>

l4(self) == /\ pc[self] = "l4"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
            /\ perm_' = [perm_ EXCEPT ![self] = Head(stack[self]).perm_]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << appCP, installed, appPerms, permsInUse, 
                            appPermConsents, app_i, app_u, app, perm >>

ask(self) == l1(self) \/ l2(self) \/ l3(self) \/ l4(self)

l5(self) == /\ pc[self] = "l5"
            /\ installed' = [installed EXCEPT ![app_i[self]] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ app_i' = [app_i EXCEPT ![self] = Head(stack[self]).app_i]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << appCP, appPerms, permsInUse, appPermConsents, app_, 
                            perm_, app_u, app, perm >>

installApp(self) == l5(self)

l6(self) == /\ pc[self] = "l6"
            /\ installed' = [installed EXCEPT ![app_u[self]] = FALSE]
            /\ permsInUse' = [permsInUse EXCEPT ![app_u[self]] = [p \in Permissions |-> FALSE]]
            /\ appPermConsents' = [appPermConsents EXCEPT ![app_u[self]] = [p \in Permissions |-> NULL]]
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ app_u' = [app_u EXCEPT ![self] = Head(stack[self]).app_u]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << appCP, appPerms, app_, perm_, app_i, app, perm >>

uninstallApp(self) == l6(self)

l7(self) == /\ pc[self] = "l7"
            /\ \/ /\ \/ /\ appPerms' = [appPerms EXCEPT ![app[self]][perm[self]] = GRANT]
                        /\ appPermConsents' = [appPermConsents EXCEPT ![app[self]][perm[self]] = ALLOW]
                     \/ /\ appPerms' = [appPerms EXCEPT ![app[self]][perm[self]] = DENY]
                        /\ appPermConsents' = [appPermConsents EXCEPT ![app[self]][perm[self]] = REJECT]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                  /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               \/ /\ \/ /\ appPerms' = [appPerms EXCEPT ![app[self]][perm[self]] = GRANT]
                        /\ appPermConsents' = [appPermConsents EXCEPT ![app[self]][perm[self]] = ALLOW]
                     \/ /\ appPerms' = [appPerms EXCEPT ![app[self]][perm[self]] = DENY]
                        /\ appPermConsents' = [appPermConsents EXCEPT ![app[self]][perm[self]] = REJECT]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                  /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << appCP, installed, permsInUse, app_, perm_, app_i, 
                            app_u >>

makeDecision(self) == l7(self)

platform(self) == /\ pc[self] = "platform"
                  /\ IF ~appInstalled(self)
                        THEN /\ /\ app_i' = [app_i EXCEPT ![self] = self]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "installApp",
                                                                         pc        |->  "platform",
                                                                         app_i     |->  app_i[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "l5"]
                             /\ UNCHANGED << appCP, app_, perm_, app_u >>
                        ELSE /\ \/ /\ /\ app_u' = [app_u EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                               pc        |->  "platform",
                                                                               app_u     |->  app_u[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "l6"]
                                   /\ UNCHANGED <<appCP, app_, perm_>>
                                \/ /\ \/ /\ IF appCP[self] = NULL
                                               THEN /\ \/ /\ appCP' = [appCP EXCEPT ![self] = NORMAL]
                                                       \/ /\ appCP' = [appCP EXCEPT ![self] = SENSITIVE]
                                               ELSE /\ appCP' = [appCP EXCEPT ![self] = NULL]
                                         /\ pc' = [pc EXCEPT ![self] = "platform"]
                                         /\ UNCHANGED <<stack, app_, perm_>>
                                      \/ /\ \/ /\ IF appCP[self] = NULL
                                                     THEN /\ \/ /\ appCP' = [appCP EXCEPT ![self] = NORMAL]
                                                             \/ /\ appCP' = [appCP EXCEPT ![self] = SENSITIVE]
                                                     ELSE /\ TRUE
                                                          /\ appCP' = appCP
                                               /\ pc' = [pc EXCEPT ![self] = "platform"]
                                               /\ UNCHANGED <<stack, app_, perm_>>
                                            \/ /\ \E p \in Permissions:
                                                    /\ /\ app_' = [app_ EXCEPT ![self] = self]
                                                       /\ perm_' = [perm_ EXCEPT ![self] = p]
                                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ask",
                                                                                                pc        |->  "platform",
                                                                                                app_      |->  app_[self],
                                                                                                perm_     |->  perm_[self] ] >>
                                                                                            \o stack[self]]
                                                    /\ pc' = [pc EXCEPT ![self] = "l1"]
                                               /\ appCP' = appCP
                                   /\ app_u' = app_u
                             /\ app_i' = app_i
                  /\ UNCHANGED << installed, appPerms, permsInUse, 
                                  appPermConsents, app, perm >>

a(self) == platform(self)

Next == (\E self \in ProcSet:  \/ ask(self) \/ installApp(self)
                               \/ uninstallApp(self) \/ makeDecision(self))
           \/ (\E self \in Applications: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : /\ WF_vars((pc[self] # "platform") /\ a(self))
                                      /\ WF_vars(installApp(self))
                                      /\ WF_vars(uninstallApp(self))
                                      /\ WF_vars(ask(self))
                                      /\ WF_vars(makeDecision(self))

\* END TRANSLATION

TypeOK == /\ appPerms \in [Applications -> [Permissions -> PermissionRequestDecision]]
          /\ appPermConsents \in [Applications -> [Permissions -> UserConsent]]
          /\ permsInUse \in [Applications -> [Permissions -> Boolean]]
          /\ appCP \in [Applications -> CustomPermission]
          /\ installed \in [Applications -> Boolean]

UserAgreed == [] ~(/\ \E application \in Applications : \E permission \in Permissions :
                      /\ appPermConsents[application][permission] # ALLOW
                      /\ appPerms[application][permission] = GRANT
                      /\ permsInUse[application][permission] = TRUE)

CpUserAgreed == [] ~(/\ \E application \in Applications : \E permission \in Permissions :
                        /\ appCP[application] = SENSITIVE
                        /\ appPerms[application][permission] = GRANT
                        /\ permsInUse[application][permission] = TRUE
                        /\ appPermConsents[application][permission] # ALLOW)

Authorized == [] ~(/\ \E application \in Applications : \E permission \in Permissions :
                      /\ appPerms[application][permission] # GRANT
                      /\ permsInUse[application][permission] = TRUE)
                      
=============================================================================
\* Modification History
\* Last modified Sat Mar 18 21:34:58 IRST 2023 by Amirhosein
