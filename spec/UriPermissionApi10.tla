--------------------------- MODULE UriPermissionApi10 ---------------------------
EXTENDS Naturals, Sequences

CONSTANTS A, P, Uri, ModeFlag

ASSUME A \in Nat
ASSUME P \in Nat

Permissions == 1..P
Applications == 1..A
UriPermissions == Uri
Flags == ModeFlag

NULL == "NULL"
DENY == "DENY"
GRANT == "GRANT"
ALLOW == "ALLOW"
REJECT == "REJECT"
NORMAL == "NORMAL"
SENSITIVE == "SENSITIVE"

Boolean == { TRUE, FALSE }
Consent == { ALLOW, REJECT, NULL }
CustomPermission == { NORMAL, SENSITIVE, NULL }
PermissionRequestDecision == { GRANT, DENY, NULL }
UriPermissionSignature == Flags \cup { NULL }

(***       this is a comment containing the PlusCal code *

--algorithm PermissionManager
{
    variables CP = [a \in Applications |-> NULL];
              installed = [p \in Applications |-> FALSE];
              appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]];
              permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]];
              cpConsent = [a \in Applications |-> [aa \in Applications |-> NULL]];
              appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]];
              appCustomPerms = [i \in Applications |-> [i2 \in Applications |-> NULL]];
              manifest = [i \in Applications |-> [M \in Flags |-> NULL]];

    procedure installApp(app)
    {
        INSTALL_APP: installed[app] := TRUE; return;
        DEFINE_URI_PERM: with (u \in UriPermissions) { manifest[self] := u };
    }
    
    procedure defineCP(app) { DEFINE_CP: return; }
               
    procedure askCpFromUser(a1, a2) { ASK_CP_FROM_USER: return; }
               
    procedure updateApp(app) { UPDATE_APP: return; }
    
    procedure askAppCP(a1, a2) { ASK_APP_CP: return; }
    
    procedure uninstallApp(app)
    {
        UNINSTALL_APP: installed[app] := FALSE;
                       permsInUse[app] := [p \in Permissions |-> FALSE];
                       appPermConsents[app] := [p \in Permissions |-> NULL];
                       return;
    }
    
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
    
    procedure grantUriPermission(targetApp, uri, modeFlag)
    {
        \*DETERMINE_DECISION: call systemArbitraryDecision(target);
        \*USE_PERMISSION: call askPermission(self);
        GRANT_URI_PERMISSION: return;
    }
    
    fair process (a \in Applications)
    {        
        PLATFORM:- while (TRUE)
        {
            if(installed[self] = TRUE)
            {
                either { call uninstallApp(self) }
                or { with (u \in UriPermissions)
                     with (m \in Flags) { call grantUriPermission(self, u, m); } }
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
\* BEGIN TRANSLATION (chksum(pcal) = "c9d93315" /\ chksum(tla) = "19051cc3")
\* Parameter app of procedure installApp at line 41 col 26 changed to app_
\* Parameter app of procedure defineCP at line 47 col 24 changed to app_d
\* Parameter a1 of procedure askCpFromUser at line 49 col 29 changed to a1_
\* Parameter a2 of procedure askCpFromUser at line 49 col 33 changed to a2_
\* Parameter app of procedure updateApp at line 51 col 25 changed to app_u
\* Parameter app of procedure uninstallApp at line 55 col 28 changed to app_un
\* Parameter app of procedure systemArbitraryDecision at line 63 col 39 changed to app_s
\* Parameter perm of procedure systemArbitraryDecision at line 63 col 44 changed to perm_
CONSTANT defaultInitValue
VARIABLES CP, installed, appPerms, permsInUse, cpConsent, appPermConsents, 
          appCustomPerms, manifest, pc, stack, app_, app_d, a1_, a2_, app_u, 
          a1, a2, app_un, app_s, perm_, app, perm, targetApp, uri, modeFlag

vars == << CP, installed, appPerms, permsInUse, cpConsent, appPermConsents, 
           appCustomPerms, manifest, pc, stack, app_, app_d, a1_, a2_, app_u, 
           a1, a2, app_un, app_s, perm_, app, perm, targetApp, uri, modeFlag
        >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ CP = [a \in Applications |-> NULL]
        /\ installed = [p \in Applications |-> FALSE]
        /\ appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]]
        /\ permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]]
        /\ cpConsent = [a \in Applications |-> [aa \in Applications |-> NULL]]
        /\ appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]]
        /\ appCustomPerms = [i \in Applications |-> [i2 \in Applications |-> NULL]]
        /\ manifest = [i \in Applications |-> [M \in Flags |-> NULL]]
        (* Procedure installApp *)
        /\ app_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure defineCP *)
        /\ app_d = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askCpFromUser *)
        /\ a1_ = [ self \in ProcSet |-> defaultInitValue]
        /\ a2_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure updateApp *)
        /\ app_u = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askAppCP *)
        /\ a1 = [ self \in ProcSet |-> defaultInitValue]
        /\ a2 = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure uninstallApp *)
        /\ app_un = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure systemArbitraryDecision *)
        /\ app_s = [ self \in ProcSet |-> defaultInitValue]
        /\ perm_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askPermission *)
        /\ app = [ self \in ProcSet |-> defaultInitValue]
        /\ perm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure grantUriPermission *)
        /\ targetApp = [ self \in ProcSet |-> defaultInitValue]
        /\ uri = [ self \in ProcSet |-> defaultInitValue]
        /\ modeFlag = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "PLATFORM"]

INSTALL_APP(self) == /\ pc[self] = "INSTALL_APP"
                     /\ installed' = [installed EXCEPT ![app_[self]] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << CP, appPerms, permsInUse, cpConsent, 
                                     appPermConsents, appCustomPerms, manifest, 
                                     app_d, a1_, a2_, app_u, a1, a2, app_un, 
                                     app_s, perm_, app, perm, targetApp, uri, 
                                     modeFlag >>

DEFINE_URI_PERM(self) == /\ pc[self] = "DEFINE_URI_PERM"
                         /\ \E u \in UriPermissions:
                              manifest' = [manifest EXCEPT ![self] = u]
                         /\ pc' = [pc EXCEPT ![self] = "Error"]
                         /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                         cpConsent, appPermConsents, 
                                         appCustomPerms, stack, app_, app_d, 
                                         a1_, a2_, app_u, a1, a2, app_un, 
                                         app_s, perm_, app, perm, targetApp, 
                                         uri, modeFlag >>

installApp(self) == INSTALL_APP(self) \/ DEFINE_URI_PERM(self)

DEFINE_CP(self) == /\ pc[self] = "DEFINE_CP"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ app_d' = [app_d EXCEPT ![self] = Head(stack[self]).app_d]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                   cpConsent, appPermConsents, appCustomPerms, 
                                   manifest, app_, a1_, a2_, app_u, a1, a2, 
                                   app_un, app_s, perm_, app, perm, targetApp, 
                                   uri, modeFlag >>

defineCP(self) == DEFINE_CP(self)

ASK_CP_FROM_USER(self) == /\ pc[self] = "ASK_CP_FROM_USER"
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ a1_' = [a1_ EXCEPT ![self] = Head(stack[self]).a1_]
                          /\ a2_' = [a2_ EXCEPT ![self] = Head(stack[self]).a2_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                          cpConsent, appPermConsents, 
                                          appCustomPerms, manifest, app_, 
                                          app_d, app_u, a1, a2, app_un, app_s, 
                                          perm_, app, perm, targetApp, uri, 
                                          modeFlag >>

askCpFromUser(self) == ASK_CP_FROM_USER(self)

UPDATE_APP(self) == /\ pc[self] = "UPDATE_APP"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_u' = [app_u EXCEPT ![self] = Head(stack[self]).app_u]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                    cpConsent, appPermConsents, appCustomPerms, 
                                    manifest, app_, app_d, a1_, a2_, a1, a2, 
                                    app_un, app_s, perm_, app, perm, targetApp, 
                                    uri, modeFlag >>

updateApp(self) == UPDATE_APP(self)

ASK_APP_CP(self) == /\ pc[self] = "ASK_APP_CP"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ a1' = [a1 EXCEPT ![self] = Head(stack[self]).a1]
                    /\ a2' = [a2 EXCEPT ![self] = Head(stack[self]).a2]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                    cpConsent, appPermConsents, appCustomPerms, 
                                    manifest, app_, app_d, a1_, a2_, app_u, 
                                    app_un, app_s, perm_, app, perm, targetApp, 
                                    uri, modeFlag >>

askAppCP(self) == ASK_APP_CP(self)

UNINSTALL_APP(self) == /\ pc[self] = "UNINSTALL_APP"
                       /\ installed' = [installed EXCEPT ![app_un[self]] = FALSE]
                       /\ permsInUse' = [permsInUse EXCEPT ![app_un[self]] = [p \in Permissions |-> FALSE]]
                       /\ appPermConsents' = [appPermConsents EXCEPT ![app_un[self]] = [p \in Permissions |-> NULL]]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app_un' = [app_un EXCEPT ![self] = Head(stack[self]).app_un]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << CP, appPerms, cpConsent, appCustomPerms, 
                                       manifest, app_, app_d, a1_, a2_, app_u, 
                                       a1, a2, app_s, perm_, app, perm, 
                                       targetApp, uri, modeFlag >>

uninstallApp(self) == UNINSTALL_APP(self)

SYSTEM_ARBITRARY_DECISION(self) == /\ pc[self] = "SYSTEM_ARBITRARY_DECISION"
                                   /\ \/ /\ appPerms' = [appPerms EXCEPT ![app_s[self]][perm_[self]] = GRANT]
                                         /\ appPermConsents' = [appPermConsents EXCEPT ![app_s[self]][perm_[self]] = ALLOW]
                                      \/ /\ appPerms' = [appPerms EXCEPT ![app_s[self]][perm_[self]] = DENY]
                                         /\ appPermConsents' = [appPermConsents EXCEPT ![app_s[self]][perm_[self]] = REJECT]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ app_s' = [app_s EXCEPT ![self] = Head(stack[self]).app_s]
                                   /\ perm_' = [perm_ EXCEPT ![self] = Head(stack[self]).perm_]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << CP, installed, permsInUse, 
                                                   cpConsent, appCustomPerms, 
                                                   manifest, app_, app_d, a1_, 
                                                   a2_, app_u, a1, a2, app_un, 
                                                   app, perm, targetApp, uri, 
                                                   modeFlag >>

systemArbitraryDecision(self) == SYSTEM_ARBITRARY_DECISION(self)

ASK_PERMISSION(self) == /\ pc[self] = "ASK_PERMISSION"
                        /\ IF appPerms[app[self]][perm[self]] = GRANT
                              THEN /\ permsInUse' = [permsInUse EXCEPT ![app[self]][perm[self]] = TRUE]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                                   /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ IF appPerms[app[self]][perm[self]] = DENY
                                         THEN /\ permsInUse' = [permsInUse EXCEPT ![app[self]][perm[self]] = FALSE]
                                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                              /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                                              /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "MAKE_DECISION"]
                                              /\ UNCHANGED << permsInUse, 
                                                              stack, app, perm >>
                        /\ UNCHANGED << CP, installed, appPerms, cpConsent, 
                                        appPermConsents, appCustomPerms, 
                                        manifest, app_, app_d, a1_, a2_, app_u, 
                                        a1, a2, app_un, app_s, perm_, 
                                        targetApp, uri, modeFlag >>

MAKE_DECISION(self) == /\ pc[self] = "MAKE_DECISION"
                       /\ /\ app_s' = [app_s EXCEPT ![self] = app[self]]
                          /\ perm_' = [perm_ EXCEPT ![self] = perm[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "systemArbitraryDecision",
                                                                   pc        |->  "USING_PERM",
                                                                   app_s     |->  app_s[self],
                                                                   perm_     |->  perm_[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "SYSTEM_ARBITRARY_DECISION"]
                       /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                       cpConsent, appPermConsents, 
                                       appCustomPerms, manifest, app_, app_d, 
                                       a1_, a2_, app_u, a1, a2, app_un, app, 
                                       perm, targetApp, uri, modeFlag >>

USING_PERM(self) == /\ pc[self] = "USING_PERM"
                    /\ IF appPerms[app[self]][perm[self]] = GRANT
                          THEN /\ permsInUse' = [permsInUse EXCEPT ![app[self]][perm[self]] = TRUE]
                          ELSE /\ TRUE
                               /\ UNCHANGED permsInUse
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                    /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << CP, installed, appPerms, cpConsent, 
                                    appPermConsents, appCustomPerms, manifest, 
                                    app_, app_d, a1_, a2_, app_u, a1, a2, 
                                    app_un, app_s, perm_, targetApp, uri, 
                                    modeFlag >>

askPermission(self) == ASK_PERMISSION(self) \/ MAKE_DECISION(self)
                          \/ USING_PERM(self)

GRANT_URI_PERMISSION(self) == /\ pc[self] = "GRANT_URI_PERMISSION"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ targetApp' = [targetApp EXCEPT ![self] = Head(stack[self]).targetApp]
                              /\ uri' = [uri EXCEPT ![self] = Head(stack[self]).uri]
                              /\ modeFlag' = [modeFlag EXCEPT ![self] = Head(stack[self]).modeFlag]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << CP, installed, appPerms, 
                                              permsInUse, cpConsent, 
                                              appPermConsents, appCustomPerms, 
                                              manifest, app_, app_d, a1_, a2_, 
                                              app_u, a1, a2, app_un, app_s, 
                                              perm_, app, perm >>

grantUriPermission(self) == GRANT_URI_PERMISSION(self)

PLATFORM(self) == /\ pc[self] = "PLATFORM"
                  /\ IF installed[self] = TRUE
                        THEN /\ \/ /\ /\ app_un' = [app_un EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                               pc        |->  "PLATFORM",
                                                                               app_un    |->  app_un[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "UNINSTALL_APP"]
                                   /\ UNCHANGED <<targetApp, uri, modeFlag>>
                                \/ /\ \E u \in UriPermissions:
                                        \E m \in Flags:
                                          /\ /\ modeFlag' = [modeFlag EXCEPT ![self] = m]
                                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "grantUriPermission",
                                                                                      pc        |->  "PLATFORM",
                                                                                      targetApp |->  targetApp[self],
                                                                                      uri       |->  uri[self],
                                                                                      modeFlag  |->  modeFlag[self] ] >>
                                                                                  \o stack[self]]
                                             /\ targetApp' = [targetApp EXCEPT ![self] = self]
                                             /\ uri' = [uri EXCEPT ![self] = u]
                                          /\ pc' = [pc EXCEPT ![self] = "GRANT_URI_PERMISSION"]
                                   /\ UNCHANGED app_un
                             /\ app_' = app_
                        ELSE /\ /\ app_' = [app_ EXCEPT ![self] = self]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "installApp",
                                                                         pc        |->  "PLATFORM",
                                                                         app_      |->  app_[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "INSTALL_APP"]
                             /\ UNCHANGED << app_un, targetApp, uri, modeFlag >>
                  /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                  cpConsent, appPermConsents, appCustomPerms, 
                                  manifest, app_d, a1_, a2_, app_u, a1, a2, 
                                  app_s, perm_, app, perm >>

a(self) == PLATFORM(self)

Next == (\E self \in ProcSet:  \/ installApp(self) \/ defineCP(self)
                               \/ askCpFromUser(self) \/ updateApp(self)
                               \/ askAppCP(self) \/ uninstallApp(self)
                               \/ systemArbitraryDecision(self)
                               \/ askPermission(self)
                               \/ grantUriPermission(self))
           \/ (\E self \in Applications: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : /\ WF_vars((pc[self] # "PLATFORM") /\ a(self))
                                      /\ WF_vars(uninstallApp(self))
                                      /\ WF_vars(grantUriPermission(self))
                                      /\ WF_vars(installApp(self))

\* END TRANSLATION

TypeOK == /\ appCustomPerms \in [Applications -> [Applications -> PermissionRequestDecision]]
                      
PM == INSTANCE PManager

THEOREM Spec => PM!Spec

=============================================================================
