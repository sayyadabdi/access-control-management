--------------------------- MODULE UriPermission ---------------------------
EXTENDS Naturals, Sequences

CONSTANTS Apps, Perms

NULL == "NULL"
DENY == "DENY"
GRANT == "GRANT"
ALLOW == "ALLOW"
REJECT == "REJECT"

Boolean == { TRUE, FALSE }
Consent == { ALLOW, REJECT }
PermissionRequestDecision == { GRANT, DENY, NULL }

(***       this is a comment containing the PlusCal code *

--algorithm PermissionManager
{
    variables installed = [p \in Apps |-> FALSE];
              appPerms = [i \in Apps |-> [p \in Perms |-> NULL]];
              permsInUse = [a \in Apps |-> [i \in Perms |-> FALSE]];
              appPermConsents = [a \in Apps |-> [i \in Perms |-> NULL]];
    
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
            MAKE_DECISION: call systemArbitraryDecision(app, perm);
            USING_PERM: if(appPerms[app][perm] = GRANT) { permsInUse[app][perm] := TRUE; };
            return;
        }
    }
    
    procedure uninstallApp(app)
    {
        UNINSTALL_APP: installed[app] := FALSE;
                       \*appPerms[app] := [p \in Perms |-> NULL];
                       permsInUse[app] := [p \in Perms |-> FALSE];
                       appPermConsents[app] := [p \in Perms |-> NULL];
                       return;
    }
    
    fair process (a \in Apps)
    {
        PLATFORM:- while (TRUE)
        {
            if(installed[self] = TRUE)
            {
                either { appPerms[app] := [p \in Perms |-> NULL]; call uninstallApp(self); }
                or { with (p \in Perms) { call askPermission(self, p); } }
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
\* BEGIN TRANSLATION (chksum(pcal) = "99f5cd61" /\ chksum(tla) = "c2ab5f64")
\* Parameter app of procedure installApp at line 25 col 26 changed to app_
\* Parameter app of procedure systemArbitraryDecision at line 27 col 39 changed to app_s
\* Parameter perm of procedure systemArbitraryDecision at line 27 col 44 changed to perm_
\* Parameter app of procedure askPermission at line 35 col 29 changed to app_a
CONSTANT defaultInitValue
VARIABLES installed, appPerms, permsInUse, appPermConsents, pc, stack, app_, 
          app_s, perm_, app_a, perm, app

vars == << installed, appPerms, permsInUse, appPermConsents, pc, stack, app_, 
           app_s, perm_, app_a, perm, app >>

ProcSet == (Apps)

Init == (* Global variables *)
        /\ installed = [p \in Apps |-> FALSE]
        /\ appPerms = [i \in Apps |-> [p \in Perms |-> NULL]]
        /\ permsInUse = [a \in Apps |-> [i \in Perms |-> FALSE]]
        /\ appPermConsents = [a \in Apps |-> [i \in Perms |-> NULL]]
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
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "MAKE_DECISION"]
                                              /\ UNCHANGED << permsInUse, 
                                                              stack, app_a, 
                                                              perm >>
                        /\ UNCHANGED << installed, appPerms, appPermConsents, 
                                        app_, app_s, perm_, app >>

MAKE_DECISION(self) == /\ pc[self] = "MAKE_DECISION"
                       /\ /\ app_s' = [app_s EXCEPT ![self] = app_a[self]]
                          /\ perm_' = [perm_ EXCEPT ![self] = perm[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "systemArbitraryDecision",
                                                                   pc        |->  "USING_PERM",
                                                                   app_s     |->  app_s[self],
                                                                   perm_     |->  perm_[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "SYSTEM_ARBITRARY_DECISION"]
                       /\ UNCHANGED << installed, appPerms, permsInUse, 
                                       appPermConsents, app_, app_a, perm, app >>

USING_PERM(self) == /\ pc[self] = "USING_PERM"
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

askPermission(self) == ASK_PERMISSION(self) \/ MAKE_DECISION(self)
                          \/ USING_PERM(self)

UNINSTALL_APP(self) == /\ pc[self] = "UNINSTALL_APP"
                       /\ installed' = [installed EXCEPT ![app[self]] = FALSE]
                       /\ permsInUse' = [permsInUse EXCEPT ![app[self]] = [p \in Perms |-> FALSE]]
                       /\ appPermConsents' = [appPermConsents EXCEPT ![app[self]] = [p \in Perms |-> NULL]]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << appPerms, app_, app_s, perm_, app_a, 
                                       perm >>

uninstallApp(self) == UNINSTALL_APP(self)

PLATFORM(self) == /\ pc[self] = "PLATFORM"
                  /\ IF installed[self] = TRUE
                        THEN /\ \/ /\ appPerms' = [appPerms EXCEPT ![app[self]] = [p \in Perms |-> NULL]]
                                   /\ /\ app' = [app EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                               pc        |->  "PLATFORM",
                                                                               app       |->  app[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "UNINSTALL_APP"]
                                   /\ UNCHANGED <<app_a, perm>>
                                \/ /\ \E p \in Perms:
                                        /\ /\ app_a' = [app_a EXCEPT ![self] = self]
                                           /\ perm' = [perm EXCEPT ![self] = p]
                                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "askPermission",
                                                                                    pc        |->  "PLATFORM",
                                                                                    app_a     |->  app_a[self],
                                                                                    perm      |->  perm[self] ] >>
                                                                                \o stack[self]]
                                        /\ pc' = [pc EXCEPT ![self] = "ASK_PERMISSION"]
                                   /\ UNCHANGED <<appPerms, app>>
                             /\ app_' = app_
                        ELSE /\ /\ app_' = [app_ EXCEPT ![self] = self]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "installApp",
                                                                         pc        |->  "PLATFORM",
                                                                         app_      |->  app_[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "INSTALL_APP"]
                             /\ UNCHANGED << appPerms, app_a, perm, app >>
                  /\ UNCHANGED << installed, permsInUse, appPermConsents, 
                                  app_s, perm_ >>

a(self) == PLATFORM(self)

Next == (\E self \in ProcSet:  \/ installApp(self)
                               \/ systemArbitraryDecision(self)
                               \/ askPermission(self) \/ uninstallApp(self))
           \/ (\E self \in Apps: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Apps : /\ WF_vars((pc[self] # "PLATFORM") /\ a(self))
                              /\ WF_vars(uninstallApp(self))
                              /\ WF_vars(askPermission(self))
                              /\ WF_vars(installApp(self))
                              /\ WF_vars(systemArbitraryDecision(self))

\* END TRANSLATION

TypeOK == /\ installed \in [Apps -> Boolean]
          /\ appPerms \in [Apps -> [Perms -> PermissionRequestDecision]]
          /\ appPermConsents \in [Apps -> [Perms -> Consent \cup { NULL }]]
          /\ permsInUse \in [Apps -> [Perms -> Boolean]]

UriPermConsent == [] ~(/\ \E application \in Apps : \E permission \in Perms : \* Bagheri
                          /\ appPermConsents[application][permission] # ALLOW
                          /\ appPerms[application][permission] = GRANT
                          /\ permsInUse[application][permission] = TRUE)

Authorized == [] ~(/\ \E application \in Apps : \E permission \in Perms : \* System consent
                      /\ appPerms[application][permission] # GRANT
                      /\ permsInUse[application][permission] = TRUE)
                      
ACL == appPermConsents
Resource == permsInUse
                      
ACM == INSTANCE AccessControlManagement

THEOREM Spec => ACM!Spec
=============================================================================
\* Modification History
\* Last modified Thu Mar 23 11:30:20 GMT+03:30 2023 by Amirhosein
