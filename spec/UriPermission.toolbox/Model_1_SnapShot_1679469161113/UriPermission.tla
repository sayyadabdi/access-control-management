--------------------------- MODULE UriPermission ---------------------------
EXTENDS Naturals, Sequences

CONSTANTS A, P
 
ASSUME A \in Nat
ASSUME P \in Nat

Permissions == 1..P
Applications == 1..A

NULL == "NULL"
DENY == "DENY"
GRANT == "GRANT"
ALLOW == "ALLOW"
REJECT == "REJECT"

Boolean == { TRUE, FALSE }
Consent == { ALLOW, REJECT, NULL }
PermissionRequestDecision == { GRANT, DENY, NULL }

(***       this is a comment containing the PlusCal code *

--algorithm PermissionManager
{
    variables installed = [p \in Applications |-> FALSE];
              appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]];
              permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]];
              appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]];
    
    procedure installApp(app) { INSTALL_APP: installed[app] := TRUE; return; }
    
    procedure systemArbitraryDecision(app, perm)
    {
        SYSTEM_ARBITRARY_DECISION:
        either { appPerms[app][perm] := GRANT; appPermConsents[app][perm] := ALLOW; }
        or { appPerms[app][perm] := DENY; appPermConsents[app][perm] := REJECT; };
        return;
    }

    
    procedure askPermission(app, perm)
    {
        ASK_PERMISSION:
        if(appPerms[app][perm] = GRANT) { permsInUse[app][perm] := TRUE; return }
        else if(appPerms[app][perm] = DENY) { permsInUse[app][perm] := FALSE; return }
        else
        {
            make_decision: call systemArbitraryDecision(app, perm);
            using_perm: if(appPerms[app][perm] = GRANT) { permsInUse[app][perm] := TRUE; };
            return;
        }
    }
    
    procedure uninstallApp(app)
    {
        UNINSTALL_APP: installed[app] := FALSE;
                       appPerms[app] := [p \in Permissions |-> NULL];
                       permsInUse[app] := [p \in Permissions |-> FALSE];
                       appPermConsents[app] := [p \in Permissions |-> NULL];
                       return;
    }
    
    fair process (a \in Applications)
    {
        PLATFORM:- while (TRUE)
        {
            if(installed[self] = TRUE)
            {
                either { call uninstallApp(self); }
                or { with (p \in Permissions) { call askPermission(self, p); } }
            }
            else
            {
                call installApp(self);
            }
        };
    }
}

    this ends the comment containing the PlusCal code
*************)             
\* BEGIN TRANSLATION (chksum(pcal) = "1890a543" /\ chksum(tla) = "2ec0404e")
\* Parameter app of procedure installApp at line 31 col 26 changed to app_
\* Parameter app of procedure systemArbitraryDecision at line 33 col 39 changed to app_s
\* Parameter perm of procedure systemArbitraryDecision at line 33 col 44 changed to perm_
\* Parameter app of procedure askPermission at line 42 col 29 changed to app_a
CONSTANT defaultInitValue
VARIABLES installed, appPerms, permsInUse, appPermConsents, pc, stack, app_, 
          app_s, perm_, app_a, perm, app

vars == << installed, appPerms, permsInUse, appPermConsents, pc, stack, app_, 
           app_s, perm_, app_a, perm, app >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ installed = [p \in Applications |-> FALSE]
        /\ appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]]
        /\ permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]]
        /\ appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]]
        (* Procedure installApp *)
        /\ app_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure systemArbitraryDecision *)
        /\ app_s = [ self \in ProcSet |-> defaultInitValue]
        /\ perm_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askPermission *)
        /\ app_a = [ self \in ProcSet |-> defaultInitValue]
        /\ perm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure uninstallApp *)
        /\ app = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "PLATFORM"]

INSTALL_APP(self) == /\ pc[self] = "INSTALL_APP"
                     /\ installed' = [installed EXCEPT ![app_[self]] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << appPerms, permsInUse, appPermConsents, 
                                     app_s, perm_, app_a, perm, app >>

installApp(self) == INSTALL_APP(self)

SYSTEM_ARBITRARY_DECISION(self) == /\ pc[self] = "SYSTEM_ARBITRARY_DECISION"
                                   /\ \/ /\ appPerms' = [appPerms EXCEPT ![app_s[self]][perm_[self]] = GRANT]
                                         /\ appPermConsents' = [appPermConsents EXCEPT ![app_s[self]][perm_[self]] = ALLOW]
                                      \/ /\ appPerms' = [appPerms EXCEPT ![app_s[self]][perm_[self]] = DENY]
                                         /\ appPermConsents' = [appPermConsents EXCEPT ![app_s[self]][perm_[self]] = REJECT]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ app_s' = [app_s EXCEPT ![self] = Head(stack[self]).app_s]
                                   /\ perm_' = [perm_ EXCEPT ![self] = Head(stack[self]).perm_]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << installed, permsInUse, app_, 
                                                   app_a, perm, app >>

systemArbitraryDecision(self) == SYSTEM_ARBITRARY_DECISION(self)

ASK_PERMISSION(self) == /\ pc[self] = "ASK_PERMISSION"
                        /\ IF appPerms[app_a[self]][perm[self]] = GRANT
                              THEN /\ permsInUse' = [permsInUse EXCEPT ![app_a[self]][perm[self]] = TRUE]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ app_a' = [app_a EXCEPT ![self] = Head(stack[self]).app_a]
                                   /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ IF appPerms[app_a[self]][perm[self]] = DENY
                                         THEN /\ permsInUse' = [permsInUse EXCEPT ![app_a[self]][perm[self]] = FALSE]
                                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                              /\ app_a' = [app_a EXCEPT ![self] = Head(stack[self]).app_a]
                                              /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "make_decision"]
                                              /\ UNCHANGED << permsInUse, 
                                                              stack, app_a, 
                                                              perm >>
                        /\ UNCHANGED << installed, appPerms, appPermConsents, 
                                        app_, app_s, perm_, app >>

make_decision(self) == /\ pc[self] = "make_decision"
                       /\ /\ app_s' = [app_s EXCEPT ![self] = app_a[self]]
                          /\ perm_' = [perm_ EXCEPT ![self] = perm[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "systemArbitraryDecision",
                                                                   pc        |->  "using_perm",
                                                                   app_s     |->  app_s[self],
                                                                   perm_     |->  perm_[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "SYSTEM_ARBITRARY_DECISION"]
                       /\ UNCHANGED << installed, appPerms, permsInUse, 
                                       appPermConsents, app_, app_a, perm, app >>

using_perm(self) == /\ pc[self] = "using_perm"
                    /\ IF appPerms[app_a[self]][perm[self]] = GRANT
                          THEN /\ permsInUse' = [permsInUse EXCEPT ![app_a[self]][perm[self]] = TRUE]
                          ELSE /\ TRUE
                               /\ UNCHANGED permsInUse
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_a' = [app_a EXCEPT ![self] = Head(stack[self]).app_a]
                    /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << installed, appPerms, appPermConsents, app_, 
                                    app_s, perm_, app >>

askPermission(self) == ASK_PERMISSION(self) \/ make_decision(self)
                          \/ using_perm(self)

UNINSTALL_APP(self) == /\ pc[self] = "UNINSTALL_APP"
                       /\ installed' = [installed EXCEPT ![app[self]] = FALSE]
                       /\ appPerms' = [appPerms EXCEPT ![app[self]] = [p \in Permissions |-> NULL]]
                       /\ permsInUse' = [permsInUse EXCEPT ![app[self]] = [p \in Permissions |-> FALSE]]
                       /\ appPermConsents' = [appPermConsents EXCEPT ![app[self]] = [p \in Permissions |-> NULL]]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << app_, app_s, perm_, app_a, perm >>

uninstallApp(self) == UNINSTALL_APP(self)

PLATFORM(self) == /\ pc[self] = "PLATFORM"
                  /\ IF installed[self] = TRUE
                        THEN /\ \/ /\ /\ app' = [app EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                               pc        |->  "PLATFORM",
                                                                               app       |->  app[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "UNINSTALL_APP"]
                                   /\ UNCHANGED <<app_a, perm>>
                                \/ /\ \E p \in Permissions:
                                        /\ /\ app_a' = [app_a EXCEPT ![self] = self]
                                           /\ perm' = [perm EXCEPT ![self] = p]
                                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "askPermission",
                                                                                    pc        |->  "PLATFORM",
                                                                                    app_a     |->  app_a[self],
                                                                                    perm      |->  perm[self] ] >>
                                                                                \o stack[self]]
                                        /\ pc' = [pc EXCEPT ![self] = "ASK_PERMISSION"]
                                   /\ app' = app
                             /\ app_' = app_
                        ELSE /\ /\ app_' = [app_ EXCEPT ![self] = self]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "installApp",
                                                                         pc        |->  "PLATFORM",
                                                                         app_      |->  app_[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "INSTALL_APP"]
                             /\ UNCHANGED << app_a, perm, app >>
                  /\ UNCHANGED << installed, appPerms, permsInUse, 
                                  appPermConsents, app_s, perm_ >>

a(self) == PLATFORM(self)

Next == (\E self \in ProcSet:  \/ installApp(self)
                               \/ systemArbitraryDecision(self)
                               \/ askPermission(self) \/ uninstallApp(self))
           \/ (\E self \in Applications: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : /\ WF_vars((pc[self] # "PLATFORM") /\ a(self))
                                      /\ WF_vars(uninstallApp(self))
                                      /\ WF_vars(askPermission(self))
                                      /\ WF_vars(installApp(self))
                                      /\ WF_vars(systemArbitraryDecision(self))

\* END TRANSLATION

TypeOK == /\ installed \in [Applications -> Boolean]
          /\ appPerms \in [Applications -> [Permissions -> PermissionRequestDecision]]
          /\ appPermConsents \in [Applications -> [Permissions -> Consent]]
          /\ permsInUse \in [Applications -> [Permissions -> Boolean]]

UriPermConsent == [] ~(/\ \E application \in Applications : \E permission \in Permissions : \* Bagheri
                          /\ appPermConsents[application][permission] # ALLOW
                          /\ appPerms[application][permission] = GRANT
                          /\ permsInUse[application][permission] = TRUE)

Authorized == [] ~(/\ \E application \in Applications : \E permission \in Permissions : \* System consent
                      /\ appPerms[application][permission] # GRANT
                      /\ permsInUse[application][permission] = TRUE)               
=============================================================================
\* Modification History
\* Last modified Wed Mar 22 10:42:33 GMT+03:30 2023 by Amirhosein
