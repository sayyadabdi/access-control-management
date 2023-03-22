------------------------------ MODULE PManager ------------------------------
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
NORMAL == "NORMAL"
SENSITIVE == "SENSITIVE"

Boolean == { TRUE, FALSE }
UserConsent == { ALLOW, REJECT, NULL }
CustomPermission == { NORMAL, SENSITIVE, NULL }
PermissionRequestDecision == { GRANT, DENY, NULL }

(***       this is a comment containing the PlusCal code *

--algorithm PermissionManager
{
    variables CP = [a \in Applications |-> NULL];
              installed = [p \in Applications |-> FALSE];
              appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]];
              permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]];
              cpUserConsent = [a \in Applications |-> [aa \in Applications |-> NULL]];
              appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]];
              appCustomPerms = [i \in Applications |-> [i2 \in Applications |-> NULL]];
    
    procedure installApp(app) { INSTALL_APP: installed[app] := TRUE; return; }
    
    procedure defineCP(app) { DEFINE_CP: either { CP[app] := NORMAL; }
                                         or { CP[app] := SENSITIVE; };
                                         return; }
                          
    procedure systemArbitraryDecision(app, perm)
    {
        SYSTEM_ARBITRARY_DECISION:
        either { appPerms[app][perm] := GRANT; appPermConsents[app][perm] := ALLOW; }
        or { appPerms[app][perm] := DENY; appPermConsents[app][perm] := REJECT; };
        return;
    }
               
    procedure askCpFromUser(a1, a2)
    {
        ASK_CP_FROM_USER:
        either { appCustomPerms[a1][a2] := GRANT; cpUserConsent[a1][a2] := ALLOW; }
        or { appCustomPerms[a1][a2] := DENY; cpUserConsent[a1][a2] := REJECT; };
        return;
    }
               
    procedure updateApp(app)
    {
        UPDATE_APP: either { CP[app] := NULL; }
                    or { call defineCP(app); };
        RETURNING:      return;
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
    
    procedure askAppCP(a1, a2)
    {
        ASK_APP_CP: if(appCustomPerms[a1][a2] = GRANT) { return; }

                    else if(appCustomPerms[a1][a2] = DENY) { return; }
        
                    else
                    {
                        if(CP[a2] = NORMAL) { appCustomPerms[a1][a2] := GRANT; };
                        else call askCpFromUser(a1, a2);
                      
                        return;
                    }
    }
    
    procedure uninstallApp(app)
    {
        UNINSTALL_APP: installed[app] := FALSE;
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
                either { call updateApp(self); }
                or { either { call uninstallApp(self); }
                     or
                     {
                        either { if(CP[self] = NULL) { call defineCP(self); } }
                        or
                        {
                            either { with (application \in (Applications \ {self})) { call askAppCP(self, application); } }
                            or { with (p \in Permissions) { call askPermission(self, p); } }
                        }
                     }
                   }
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
\* BEGIN TRANSLATION (chksum(pcal) = "2bc810d4" /\ chksum(tla) = "29878549")
\* Parameter app of procedure installApp at line 37 col 26 changed to app_
\* Parameter app of procedure defineCP at line 39 col 24 changed to app_d
\* Parameter app of procedure systemArbitraryDecision at line 43 col 39 changed to app_s
\* Parameter perm of procedure systemArbitraryDecision at line 43 col 44 changed to perm_
\* Parameter a1 of procedure askCpFromUser at line 51 col 29 changed to a1_
\* Parameter a2 of procedure askCpFromUser at line 51 col 33 changed to a2_
\* Parameter app of procedure updateApp at line 59 col 25 changed to app_u
\* Parameter app of procedure askPermission at line 66 col 29 changed to app_a
CONSTANT defaultInitValue
VARIABLES CP, installed, appPerms, permsInUse, cpUserConsent, appPermConsents, 
          appCustomPerms, pc, stack, app_, app_d, app_s, perm_, a1_, a2_, 
          app_u, app_a, perm, a1, a2, app

vars == << CP, installed, appPerms, permsInUse, cpUserConsent, 
           appPermConsents, appCustomPerms, pc, stack, app_, app_d, app_s, 
           perm_, a1_, a2_, app_u, app_a, perm, a1, a2, app >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ CP = [a \in Applications |-> NULL]
        /\ installed = [p \in Applications |-> FALSE]
        /\ appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]]
        /\ permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]]
        /\ cpUserConsent = [a \in Applications |-> [aa \in Applications |-> NULL]]
        /\ appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]]
        /\ appCustomPerms = [i \in Applications |-> [i2 \in Applications |-> NULL]]
        (* Procedure installApp *)
        /\ app_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure defineCP *)
        /\ app_d = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure systemArbitraryDecision *)
        /\ app_s = [ self \in ProcSet |-> defaultInitValue]
        /\ perm_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askCpFromUser *)
        /\ a1_ = [ self \in ProcSet |-> defaultInitValue]
        /\ a2_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure updateApp *)
        /\ app_u = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askPermission *)
        /\ app_a = [ self \in ProcSet |-> defaultInitValue]
        /\ perm = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askAppCP *)
        /\ a1 = [ self \in ProcSet |-> defaultInitValue]
        /\ a2 = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure uninstallApp *)
        /\ app = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "PLATFORM"]

INSTALL_APP(self) == /\ pc[self] = "INSTALL_APP"
                     /\ installed' = [installed EXCEPT ![app_[self]] = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << CP, appPerms, permsInUse, cpUserConsent, 
                                     appPermConsents, appCustomPerms, app_d, 
                                     app_s, perm_, a1_, a2_, app_u, app_a, 
                                     perm, a1, a2, app >>

installApp(self) == INSTALL_APP(self)

DEFINE_CP(self) == /\ pc[self] = "DEFINE_CP"
                   /\ \/ /\ CP' = [CP EXCEPT ![app_d[self]] = NORMAL]
                      \/ /\ CP' = [CP EXCEPT ![app_d[self]] = SENSITIVE]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ app_d' = [app_d EXCEPT ![self] = Head(stack[self]).app_d]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << installed, appPerms, permsInUse, 
                                   cpUserConsent, appPermConsents, 
                                   appCustomPerms, app_, app_s, perm_, a1_, 
                                   a2_, app_u, app_a, perm, a1, a2, app >>

defineCP(self) == DEFINE_CP(self)

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
                                                   cpUserConsent, 
                                                   appCustomPerms, app_, app_d, 
                                                   a1_, a2_, app_u, app_a, 
                                                   perm, a1, a2, app >>

systemArbitraryDecision(self) == SYSTEM_ARBITRARY_DECISION(self)

ASK_CP_FROM_USER(self) == /\ pc[self] = "ASK_CP_FROM_USER"
                          /\ \/ /\ appCustomPerms' = [appCustomPerms EXCEPT ![a1_[self]][a2_[self]] = GRANT]
                                /\ cpUserConsent' = [cpUserConsent EXCEPT ![a1_[self]][a2_[self]] = ALLOW]
                             \/ /\ appCustomPerms' = [appCustomPerms EXCEPT ![a1_[self]][a2_[self]] = DENY]
                                /\ cpUserConsent' = [cpUserConsent EXCEPT ![a1_[self]][a2_[self]] = REJECT]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ a1_' = [a1_ EXCEPT ![self] = Head(stack[self]).a1_]
                          /\ a2_' = [a2_ EXCEPT ![self] = Head(stack[self]).a2_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                          appPermConsents, app_, app_d, app_s, 
                                          perm_, app_u, app_a, perm, a1, a2, 
                                          app >>

askCpFromUser(self) == ASK_CP_FROM_USER(self)

UPDATE_APP(self) == /\ pc[self] = "UPDATE_APP"
                    /\ \/ /\ CP' = [CP EXCEPT ![app_u[self]] = NULL]
                          /\ pc' = [pc EXCEPT ![self] = "RETURNING"]
                          /\ UNCHANGED <<stack, app_d>>
                       \/ /\ /\ app_d' = [app_d EXCEPT ![self] = app_u[self]]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "defineCP",
                                                                      pc        |->  "RETURNING",
                                                                      app_d     |->  app_d[self] ] >>
                                                                  \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "DEFINE_CP"]
                          /\ CP' = CP
                    /\ UNCHANGED << installed, appPerms, permsInUse, 
                                    cpUserConsent, appPermConsents, 
                                    appCustomPerms, app_, app_s, perm_, a1_, 
                                    a2_, app_u, app_a, perm, a1, a2, app >>

RETURNING(self) == /\ pc[self] = "RETURNING"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ app_u' = [app_u EXCEPT ![self] = Head(stack[self]).app_u]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                   cpUserConsent, appPermConsents, 
                                   appCustomPerms, app_, app_d, app_s, perm_, 
                                   a1_, a2_, app_a, perm, a1, a2, app >>

updateApp(self) == UPDATE_APP(self) \/ RETURNING(self)

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
                        /\ UNCHANGED << CP, installed, appPerms, cpUserConsent, 
                                        appPermConsents, appCustomPerms, app_, 
                                        app_d, app_s, perm_, a1_, a2_, app_u, 
                                        a1, a2, app >>

MAKE_DECISION(self) == /\ pc[self] = "MAKE_DECISION"
                       /\ /\ app_s' = [app_s EXCEPT ![self] = app_a[self]]
                          /\ perm_' = [perm_ EXCEPT ![self] = perm[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "systemArbitraryDecision",
                                                                   pc        |->  "USING_PERM",
                                                                   app_s     |->  app_s[self],
                                                                   perm_     |->  perm_[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "SYSTEM_ARBITRARY_DECISION"]
                       /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                       cpUserConsent, appPermConsents, 
                                       appCustomPerms, app_, app_d, a1_, a2_, 
                                       app_u, app_a, perm, a1, a2, app >>

USING_PERM(self) == /\ pc[self] = "USING_PERM"
                    /\ IF appPerms[app_a[self]][perm[self]] = GRANT
                          THEN /\ permsInUse' = [permsInUse EXCEPT ![app_a[self]][perm[self]] = TRUE]
                          ELSE /\ TRUE
                               /\ UNCHANGED permsInUse
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_a' = [app_a EXCEPT ![self] = Head(stack[self]).app_a]
                    /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << CP, installed, appPerms, cpUserConsent, 
                                    appPermConsents, appCustomPerms, app_, 
                                    app_d, app_s, perm_, a1_, a2_, app_u, a1, 
                                    a2, app >>

askPermission(self) == ASK_PERMISSION(self) \/ MAKE_DECISION(self)
                          \/ USING_PERM(self)

ASK_APP_CP(self) == /\ pc[self] = "ASK_APP_CP"
                    /\ IF appCustomPerms[a1[self]][a2[self]] = GRANT
                          THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ a1' = [a1 EXCEPT ![self] = Head(stack[self]).a1]
                               /\ a2' = [a2 EXCEPT ![self] = Head(stack[self]).a2]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << appCustomPerms, a1_, a2_ >>
                          ELSE /\ IF appCustomPerms[a1[self]][a2[self]] = DENY
                                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                          /\ a1' = [a1 EXCEPT ![self] = Head(stack[self]).a1]
                                          /\ a2' = [a2 EXCEPT ![self] = Head(stack[self]).a2]
                                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                          /\ UNCHANGED << appCustomPerms, a1_, 
                                                          a2_ >>
                                     ELSE /\ IF CP[a2[self]] = NORMAL
                                                THEN /\ appCustomPerms' = [appCustomPerms EXCEPT ![a1[self]][a2[self]] = GRANT]
                                                     /\ pc' = [pc EXCEPT ![self] = "Error"]
                                                     /\ UNCHANGED << stack, 
                                                                     a1_, a2_ >>
                                                ELSE /\ /\ a1_' = [a1_ EXCEPT ![self] = a1[self]]
                                                        /\ a2_' = [a2_ EXCEPT ![self] = a2[self]]
                                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "askCpFromUser",
                                                                                                 pc        |->  Head(stack[self]).pc,
                                                                                                 a1_       |->  a1_[self],
                                                                                                 a2_       |->  a2_[self] ] >>
                                                                                             \o Tail(stack[self])]
                                                     /\ pc' = [pc EXCEPT ![self] = "ASK_CP_FROM_USER"]
                                                     /\ UNCHANGED appCustomPerms
                                          /\ UNCHANGED << a1, a2 >>
                    /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                    cpUserConsent, appPermConsents, app_, 
                                    app_d, app_s, perm_, app_u, app_a, perm, 
                                    app >>

askAppCP(self) == ASK_APP_CP(self)

UNINSTALL_APP(self) == /\ pc[self] = "UNINSTALL_APP"
                       /\ installed' = [installed EXCEPT ![app[self]] = FALSE]
                       /\ permsInUse' = [permsInUse EXCEPT ![app[self]] = [p \in Permissions |-> FALSE]]
                       /\ appPermConsents' = [appPermConsents EXCEPT ![app[self]] = [p \in Permissions |-> NULL]]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << CP, appPerms, cpUserConsent, 
                                       appCustomPerms, app_, app_d, app_s, 
                                       perm_, a1_, a2_, app_u, app_a, perm, a1, 
                                       a2 >>

uninstallApp(self) == UNINSTALL_APP(self)

PLATFORM(self) == /\ pc[self] = "PLATFORM"
                  /\ IF installed[self] = TRUE
                        THEN /\ \/ /\ /\ app_u' = [app_u EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateApp",
                                                                               pc        |->  "PLATFORM",
                                                                               app_u     |->  app_u[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "UPDATE_APP"]
                                   /\ UNCHANGED <<app_d, app_a, perm, a1, a2, app>>
                                \/ /\ \/ /\ /\ app' = [app EXCEPT ![self] = self]
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                                     pc        |->  "PLATFORM",
                                                                                     app       |->  app[self] ] >>
                                                                                 \o stack[self]]
                                         /\ pc' = [pc EXCEPT ![self] = "UNINSTALL_APP"]
                                         /\ UNCHANGED <<app_d, app_a, perm, a1, a2>>
                                      \/ /\ \/ /\ IF CP[self] = NULL
                                                     THEN /\ /\ app_d' = [app_d EXCEPT ![self] = self]
                                                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "defineCP",
                                                                                                      pc        |->  "PLATFORM",
                                                                                                      app_d     |->  app_d[self] ] >>
                                                                                                  \o stack[self]]
                                                          /\ pc' = [pc EXCEPT ![self] = "DEFINE_CP"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "PLATFORM"]
                                                          /\ UNCHANGED << stack, 
                                                                          app_d >>
                                               /\ UNCHANGED <<app_a, perm, a1, a2>>
                                            \/ /\ \/ /\ \E application \in (Applications \ {self}):
                                                          /\ /\ a1' = [a1 EXCEPT ![self] = self]
                                                             /\ a2' = [a2 EXCEPT ![self] = application]
                                                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "askAppCP",
                                                                                                      pc        |->  "PLATFORM",
                                                                                                      a1        |->  a1[self],
                                                                                                      a2        |->  a2[self] ] >>
                                                                                                  \o stack[self]]
                                                          /\ pc' = [pc EXCEPT ![self] = "ASK_APP_CP"]
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
                                                     /\ UNCHANGED <<a1, a2>>
                                               /\ app_d' = app_d
                                         /\ app' = app
                                   /\ app_u' = app_u
                             /\ app_' = app_
                        ELSE /\ /\ app_' = [app_ EXCEPT ![self] = self]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "installApp",
                                                                         pc        |->  "PLATFORM",
                                                                         app_      |->  app_[self] ] >>
                                                                     \o stack[self]]
                             /\ pc' = [pc EXCEPT ![self] = "INSTALL_APP"]
                             /\ UNCHANGED << app_d, app_u, app_a, perm, a1, a2, 
                                             app >>
                  /\ UNCHANGED << CP, installed, appPerms, permsInUse, 
                                  cpUserConsent, appPermConsents, 
                                  appCustomPerms, app_s, perm_, a1_, a2_ >>

a(self) == PLATFORM(self)

Next == (\E self \in ProcSet:  \/ installApp(self) \/ defineCP(self)
                               \/ systemArbitraryDecision(self)
                               \/ askCpFromUser(self) \/ updateApp(self)
                               \/ askPermission(self) \/ askAppCP(self)
                               \/ uninstallApp(self))
           \/ (\E self \in Applications: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : /\ WF_vars((pc[self] # "PLATFORM") /\ a(self))
                                      /\ WF_vars(updateApp(self))
                                      /\ WF_vars(uninstallApp(self))
                                      /\ WF_vars(defineCP(self))
                                      /\ WF_vars(askAppCP(self))
                                      /\ WF_vars(askPermission(self))
                                      /\ WF_vars(installApp(self))
                                      /\ WF_vars(askCpFromUser(self))
                                      /\ WF_vars(systemArbitraryDecision(self))

\* END TRANSLATION

TypeOK == /\ appCustomPerms \in [Applications -> [Applications -> PermissionRequestDecision]]
          /\ CP \in [Applications -> CustomPermission]
          /\ cpUserConsent \in [Applications -> [Applications -> UserConsent]]
          /\ installed \in [Applications -> Boolean]
          /\ appPerms \in [Applications -> [Permissions -> PermissionRequestDecision]]
          /\ appPermConsents \in [Applications -> [Permissions -> UserConsent]]
          /\ permsInUse \in [Applications -> [Permissions -> Boolean]]

CpConsent == [] ~(/\ \E m \in Applications : CP[m] = SENSITIVE \* Li and Tuncay (yes, simultaneously)
                     /\ \E n \in Applications :
                        /\ m # n
                        /\ appCustomPerms[n][m] = GRANT
                        /\ cpUserConsent[n][m] # ALLOW)
                            
UriPermConsent == [] ~(/\ \E application \in Applications : \E permission \in Permissions : \* Bagheri
                          /\ appPermConsents[application][permission] # ALLOW
                          /\ appPerms[application][permission] = GRANT
                          /\ permsInUse[application][permission] = TRUE)

Authorized == [] ~(/\ \E application \in Applications : \E permission \in Permissions : \* System consent
                      /\ appPerms[application][permission] # GRANT
                      /\ permsInUse[application][permission] = TRUE)               
=============================================================================
\* Modification History
\* Last modified Wed Mar 22 18:38:15 GMT+03:30 2023 by Amirhosein