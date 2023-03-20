------------------------------ MODULE PManager ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS A, P

ASSUME A \in Nat
ASSUME P \in Nat

Applications == 1..A
Permissions == 1..P

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
    variables appCustomPerms = [i \in Applications |-> [i2 \in Applications |-> NULL]];
              appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]];
              CP = [a \in Applications |-> NULL];
              cpUserConsent = [a \in Applications |-> [aa \in Applications |-> NULL]];
              appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]];
              permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]];
              installed = [p \in Applications |-> FALSE];
    
    procedure installApp(app) { INSTALL_APP: installed[app] := TRUE; return; }
    
    procedure defineCP(app) { DEFINE_CP: either { CP[app] := NORMAL; }
                                         or { CP[app] := SENSITIVE; };
                                         return; }
                          
    procedure arbitraryDecision(app, perm) { ARBITRARY_DECISION: either { appPerms[app][perm] := GRANT; appPermConsents[app][perm] := ALLOW; }
                                                                 or { appPerms[app][perm] := DENY; appPermConsents[app][perm] := REJECT; };
                                                                 return; }
               
    procedure askUser(a1, a2) { ASK_THE_USER: either { appCustomPerms[a1][a2] := GRANT; cpUserConsent[a1][a2] := ALLOW; }
                                              or { appCustomPerms[a1][a2] := DENY; cpUserConsent[a1][a2] := REJECT; };
                                              return; }
               
    procedure updateApp(app) { UPDATE_THE_APP: if(CP[app] = NULL) { call defineCP(app); }
                                               else { CP[app] := NULL; };
                               returning:      return; }
               
    procedure askPermission(app, perm)
    {
        ASK_PERMISSION: either
                        {
                            appPerms[app][perm] := GRANT;
                            appPermConsents[app][perm] := ALLOW;
                        }
                        or
                        {
                            appPerms[app][perm] := DENY;
                            appPermConsents[app][perm] := REJECT;
                        };
                        return;
    }
    
    procedure askTheUser(app, perm)
    {
        ASK_USER: if(appPerms[app][perm] = GRANT) { permsInUse[app][perm] := TRUE; return }
                  else if(appPerms[app][perm] = DENY) { permsInUse[app][perm] := FALSE; return }
                  else
                  {
                      make_decision: call makeDecision(app, perm);
                      using_perm: if(appPerms[app][perm] = GRANT) { permsInUse[app][perm] := TRUE; };
                      return;
                  }
    }
    
    procedure ask(a1, a2)
    {
        ASK_: if(appCustomPerms[a1][a2] = GRANT) { return; }

              else if(appCustomPerms[a1][a2] = DENY) { return; }
    
              else
              {
                  if(CP[a2] = NORMAL) { appCustomPerms[a1][a2] := GRANT; };
                  else call askUser(a1, a2);
                  
                  return;
              }
    }
    
    procedure makeDecision(app, perm)
    {
        MAKE_DECISION: either { call askPermission(app, perm); return }
                       or { call arbitraryDecision(app, perm); return};
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
                                    either { with (application \in (Applications \ {self})) { call ask(self, application); } }
                                    or { with (p \in Permissions) { call askTheUser(self, p); } }
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
\* BEGIN TRANSLATION (chksum(pcal) = "d3e14110" /\ chksum(tla) = "194014a4")
\* Parameter app of procedure installApp at line 37 col 26 changed to app_
\* Parameter app of procedure defineCP at line 39 col 24 changed to app_d
\* Parameter app of procedure arbitraryDecision at line 43 col 33 changed to app_a
\* Parameter perm of procedure arbitraryDecision at line 43 col 38 changed to perm_
\* Parameter a1 of procedure askUser at line 47 col 23 changed to a1_
\* Parameter a2 of procedure askUser at line 47 col 27 changed to a2_
\* Parameter app of procedure updateApp at line 51 col 25 changed to app_u
\* Parameter app of procedure askPermission at line 55 col 29 changed to app_as
\* Parameter perm of procedure askPermission at line 55 col 34 changed to perm_a
\* Parameter app of procedure askTheUser at line 70 col 26 changed to app_ask
\* Parameter perm of procedure askTheUser at line 70 col 31 changed to perm_as
\* Parameter app of procedure makeDecision at line 97 col 28 changed to app_m
CONSTANT defaultInitValue
VARIABLES appCustomPerms, appPerms, CP, cpUserConsent, appPermConsents, 
          permsInUse, installed, pc, stack, app_, app_d, app_a, perm_, a1_, 
          a2_, app_u, app_as, perm_a, app_ask, perm_as, a1, a2, app_m, perm, 
          app

vars == << appCustomPerms, appPerms, CP, cpUserConsent, appPermConsents, 
           permsInUse, installed, pc, stack, app_, app_d, app_a, perm_, a1_, 
           a2_, app_u, app_as, perm_a, app_ask, perm_as, a1, a2, app_m, perm, 
           app >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ appCustomPerms = [i \in Applications |-> [i2 \in Applications |-> NULL]]
        /\ appPerms = [i \in Applications |-> [p \in Permissions |-> NULL]]
        /\ CP = [a \in Applications |-> NULL]
        /\ cpUserConsent = [a \in Applications |-> [aa \in Applications |-> NULL]]
        /\ appPermConsents = [a \in Applications |-> [i \in Permissions |-> NULL]]
        /\ permsInUse = [a \in Applications |-> [i \in Permissions |-> FALSE]]
        /\ installed = [p \in Applications |-> FALSE]
        (* Procedure installApp *)
        /\ app_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure defineCP *)
        /\ app_d = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure arbitraryDecision *)
        /\ app_a = [ self \in ProcSet |-> defaultInitValue]
        /\ perm_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askUser *)
        /\ a1_ = [ self \in ProcSet |-> defaultInitValue]
        /\ a2_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure updateApp *)
        /\ app_u = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askPermission *)
        /\ app_as = [ self \in ProcSet |-> defaultInitValue]
        /\ perm_a = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure askTheUser *)
        /\ app_ask = [ self \in ProcSet |-> defaultInitValue]
        /\ perm_as = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure ask *)
        /\ a1 = [ self \in ProcSet |-> defaultInitValue]
        /\ a2 = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure makeDecision *)
        /\ app_m = [ self \in ProcSet |-> defaultInitValue]
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
                     /\ UNCHANGED << appCustomPerms, appPerms, CP, 
                                     cpUserConsent, appPermConsents, 
                                     permsInUse, app_d, app_a, perm_, a1_, a2_, 
                                     app_u, app_as, perm_a, app_ask, perm_as, 
                                     a1, a2, app_m, perm, app >>

installApp(self) == INSTALL_APP(self)

DEFINE_CP(self) == /\ pc[self] = "DEFINE_CP"
                   /\ \/ /\ CP' = [CP EXCEPT ![app_d[self]] = NORMAL]
                      \/ /\ CP' = [CP EXCEPT ![app_d[self]] = SENSITIVE]
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ app_d' = [app_d EXCEPT ![self] = Head(stack[self]).app_d]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << appCustomPerms, appPerms, cpUserConsent, 
                                   appPermConsents, permsInUse, installed, 
                                   app_, app_a, perm_, a1_, a2_, app_u, app_as, 
                                   perm_a, app_ask, perm_as, a1, a2, app_m, 
                                   perm, app >>

defineCP(self) == DEFINE_CP(self)

ARBITRARY_DECISION(self) == /\ pc[self] = "ARBITRARY_DECISION"
                            /\ \/ /\ appPerms' = [appPerms EXCEPT ![app_a[self]][perm_[self]] = GRANT]
                                  /\ appPermConsents' = [appPermConsents EXCEPT ![app_a[self]][perm_[self]] = ALLOW]
                               \/ /\ appPerms' = [appPerms EXCEPT ![app_a[self]][perm_[self]] = DENY]
                                  /\ appPermConsents' = [appPermConsents EXCEPT ![app_a[self]][perm_[self]] = REJECT]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ app_a' = [app_a EXCEPT ![self] = Head(stack[self]).app_a]
                            /\ perm_' = [perm_ EXCEPT ![self] = Head(stack[self]).perm_]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << appCustomPerms, CP, cpUserConsent, 
                                            permsInUse, installed, app_, app_d, 
                                            a1_, a2_, app_u, app_as, perm_a, 
                                            app_ask, perm_as, a1, a2, app_m, 
                                            perm, app >>

arbitraryDecision(self) == ARBITRARY_DECISION(self)

ASK_THE_USER(self) == /\ pc[self] = "ASK_THE_USER"
                      /\ \/ /\ appCustomPerms' = [appCustomPerms EXCEPT ![a1_[self]][a2_[self]] = GRANT]
                            /\ cpUserConsent' = [cpUserConsent EXCEPT ![a1_[self]][a2_[self]] = ALLOW]
                         \/ /\ appCustomPerms' = [appCustomPerms EXCEPT ![a1_[self]][a2_[self]] = DENY]
                            /\ cpUserConsent' = [cpUserConsent EXCEPT ![a1_[self]][a2_[self]] = REJECT]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ a1_' = [a1_ EXCEPT ![self] = Head(stack[self]).a1_]
                      /\ a2_' = [a2_ EXCEPT ![self] = Head(stack[self]).a2_]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << appPerms, CP, appPermConsents, 
                                      permsInUse, installed, app_, app_d, 
                                      app_a, perm_, app_u, app_as, perm_a, 
                                      app_ask, perm_as, a1, a2, app_m, perm, 
                                      app >>

askUser(self) == ASK_THE_USER(self)

UPDATE_THE_APP(self) == /\ pc[self] = "UPDATE_THE_APP"
                        /\ IF CP[app_u[self]] = NULL
                              THEN /\ /\ app_d' = [app_d EXCEPT ![self] = app_u[self]]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "defineCP",
                                                                               pc        |->  "returning",
                                                                               app_d     |->  app_d[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "DEFINE_CP"]
                                   /\ CP' = CP
                              ELSE /\ CP' = [CP EXCEPT ![app_u[self]] = NULL]
                                   /\ pc' = [pc EXCEPT ![self] = "returning"]
                                   /\ UNCHANGED << stack, app_d >>
                        /\ UNCHANGED << appCustomPerms, appPerms, 
                                        cpUserConsent, appPermConsents, 
                                        permsInUse, installed, app_, app_a, 
                                        perm_, a1_, a2_, app_u, app_as, perm_a, 
                                        app_ask, perm_as, a1, a2, app_m, perm, 
                                        app >>

returning(self) == /\ pc[self] = "returning"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ app_u' = [app_u EXCEPT ![self] = Head(stack[self]).app_u]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << appCustomPerms, appPerms, CP, cpUserConsent, 
                                   appPermConsents, permsInUse, installed, 
                                   app_, app_d, app_a, perm_, a1_, a2_, app_as, 
                                   perm_a, app_ask, perm_as, a1, a2, app_m, 
                                   perm, app >>

updateApp(self) == UPDATE_THE_APP(self) \/ returning(self)

ASK_PERMISSION(self) == /\ pc[self] = "ASK_PERMISSION"
                        /\ \/ /\ appPerms' = [appPerms EXCEPT ![app_as[self]][perm_a[self]] = GRANT]
                              /\ appPermConsents' = [appPermConsents EXCEPT ![app_as[self]][perm_a[self]] = ALLOW]
                           \/ /\ appPerms' = [appPerms EXCEPT ![app_as[self]][perm_a[self]] = DENY]
                              /\ appPermConsents' = [appPermConsents EXCEPT ![app_as[self]][perm_a[self]] = REJECT]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ app_as' = [app_as EXCEPT ![self] = Head(stack[self]).app_as]
                        /\ perm_a' = [perm_a EXCEPT ![self] = Head(stack[self]).perm_a]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << appCustomPerms, CP, cpUserConsent, 
                                        permsInUse, installed, app_, app_d, 
                                        app_a, perm_, a1_, a2_, app_u, app_ask, 
                                        perm_as, a1, a2, app_m, perm, app >>

askPermission(self) == ASK_PERMISSION(self)

ASK_USER(self) == /\ pc[self] = "ASK_USER"
                  /\ IF appPerms[app_ask[self]][perm_as[self]] = GRANT
                        THEN /\ permsInUse' = [permsInUse EXCEPT ![app_ask[self]][perm_as[self]] = TRUE]
                             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                             /\ app_ask' = [app_ask EXCEPT ![self] = Head(stack[self]).app_ask]
                             /\ perm_as' = [perm_as EXCEPT ![self] = Head(stack[self]).perm_as]
                             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        ELSE /\ IF appPerms[app_ask[self]][perm_as[self]] = DENY
                                   THEN /\ permsInUse' = [permsInUse EXCEPT ![app_ask[self]][perm_as[self]] = FALSE]
                                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                        /\ app_ask' = [app_ask EXCEPT ![self] = Head(stack[self]).app_ask]
                                        /\ perm_as' = [perm_as EXCEPT ![self] = Head(stack[self]).perm_as]
                                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "make_decision"]
                                        /\ UNCHANGED << permsInUse, stack, 
                                                        app_ask, perm_as >>
                  /\ UNCHANGED << appCustomPerms, appPerms, CP, cpUserConsent, 
                                  appPermConsents, installed, app_, app_d, 
                                  app_a, perm_, a1_, a2_, app_u, app_as, 
                                  perm_a, a1, a2, app_m, perm, app >>

make_decision(self) == /\ pc[self] = "make_decision"
                       /\ /\ app_m' = [app_m EXCEPT ![self] = app_ask[self]]
                          /\ perm' = [perm EXCEPT ![self] = perm_as[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "makeDecision",
                                                                   pc        |->  "using_perm",
                                                                   app_m     |->  app_m[self],
                                                                   perm      |->  perm[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "MAKE_DECISION"]
                       /\ UNCHANGED << appCustomPerms, appPerms, CP, 
                                       cpUserConsent, appPermConsents, 
                                       permsInUse, installed, app_, app_d, 
                                       app_a, perm_, a1_, a2_, app_u, app_as, 
                                       perm_a, app_ask, perm_as, a1, a2, app >>

using_perm(self) == /\ pc[self] = "using_perm"
                    /\ IF appPerms[app_ask[self]][perm_as[self]] = GRANT
                          THEN /\ permsInUse' = [permsInUse EXCEPT ![app_ask[self]][perm_as[self]] = TRUE]
                          ELSE /\ TRUE
                               /\ UNCHANGED permsInUse
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_ask' = [app_ask EXCEPT ![self] = Head(stack[self]).app_ask]
                    /\ perm_as' = [perm_as EXCEPT ![self] = Head(stack[self]).perm_as]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << appCustomPerms, appPerms, CP, 
                                    cpUserConsent, appPermConsents, installed, 
                                    app_, app_d, app_a, perm_, a1_, a2_, app_u, 
                                    app_as, perm_a, a1, a2, app_m, perm, app >>

askTheUser(self) == ASK_USER(self) \/ make_decision(self)
                       \/ using_perm(self)

ASK_(self) == /\ pc[self] = "ASK_"
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
                                    /\ UNCHANGED << appCustomPerms, a1_, a2_ >>
                               ELSE /\ IF CP[a2[self]] = NORMAL
                                          THEN /\ appCustomPerms' = [appCustomPerms EXCEPT ![a1[self]][a2[self]] = GRANT]
                                               /\ pc' = [pc EXCEPT ![self] = "Error"]
                                               /\ UNCHANGED << stack, a1_, a2_ >>
                                          ELSE /\ /\ a1_' = [a1_ EXCEPT ![self] = a1[self]]
                                                  /\ a2_' = [a2_ EXCEPT ![self] = a2[self]]
                                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "askUser",
                                                                                           pc        |->  Head(stack[self]).pc,
                                                                                           a1_       |->  a1_[self],
                                                                                           a2_       |->  a2_[self] ] >>
                                                                                       \o Tail(stack[self])]
                                               /\ pc' = [pc EXCEPT ![self] = "ASK_THE_USER"]
                                               /\ UNCHANGED appCustomPerms
                                    /\ UNCHANGED << a1, a2 >>
              /\ UNCHANGED << appPerms, CP, cpUserConsent, appPermConsents, 
                              permsInUse, installed, app_, app_d, app_a, perm_, 
                              app_u, app_as, perm_a, app_ask, perm_as, app_m, 
                              perm, app >>

ask(self) == ASK_(self)

MAKE_DECISION(self) == /\ pc[self] = "MAKE_DECISION"
                       /\ \/ /\ /\ app_as' = [app_as EXCEPT ![self] = app_m[self]]
                                /\ perm_a' = [perm_a EXCEPT ![self] = perm[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "askPermission",
                                                                         pc        |->  Head(stack[self]).pc,
                                                                         app_as    |->  app_as[self],
                                                                         perm_a    |->  perm_a[self] ] >>
                                                                     \o Tail(stack[self])]
                             /\ pc' = [pc EXCEPT ![self] = "ASK_PERMISSION"]
                             /\ UNCHANGED <<app_a, perm_>>
                          \/ /\ /\ app_a' = [app_a EXCEPT ![self] = app_m[self]]
                                /\ perm_' = [perm_ EXCEPT ![self] = perm[self]]
                                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "arbitraryDecision",
                                                                         pc        |->  Head(stack[self]).pc,
                                                                         app_a     |->  app_a[self],
                                                                         perm_     |->  perm_[self] ] >>
                                                                     \o Tail(stack[self])]
                             /\ pc' = [pc EXCEPT ![self] = "ARBITRARY_DECISION"]
                             /\ UNCHANGED <<app_as, perm_a>>
                       /\ UNCHANGED << appCustomPerms, appPerms, CP, 
                                       cpUserConsent, appPermConsents, 
                                       permsInUse, installed, app_, app_d, a1_, 
                                       a2_, app_u, app_ask, perm_as, a1, a2, 
                                       app_m, perm, app >>

makeDecision(self) == MAKE_DECISION(self)

UNINSTALL_APP(self) == /\ pc[self] = "UNINSTALL_APP"
                       /\ installed' = [installed EXCEPT ![app[self]] = FALSE]
                       /\ permsInUse' = [permsInUse EXCEPT ![app[self]] = [p \in Permissions |-> FALSE]]
                       /\ appPermConsents' = [appPermConsents EXCEPT ![app[self]] = [p \in Permissions |-> NULL]]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << appCustomPerms, appPerms, CP, 
                                       cpUserConsent, app_, app_d, app_a, 
                                       perm_, a1_, a2_, app_u, app_as, perm_a, 
                                       app_ask, perm_as, a1, a2, app_m, perm >>

uninstallApp(self) == UNINSTALL_APP(self)

PLATFORM(self) == /\ pc[self] = "PLATFORM"
                  /\ IF installed[self] = TRUE
                        THEN /\ \/ /\ /\ app_u' = [app_u EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateApp",
                                                                               pc        |->  "PLATFORM",
                                                                               app_u     |->  app_u[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "UPDATE_THE_APP"]
                                   /\ UNCHANGED <<app_d, app_ask, perm_as, a1, a2, app>>
                                \/ /\ \/ /\ /\ app' = [app EXCEPT ![self] = self]
                                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                                     pc        |->  "PLATFORM",
                                                                                     app       |->  app[self] ] >>
                                                                                 \o stack[self]]
                                         /\ pc' = [pc EXCEPT ![self] = "UNINSTALL_APP"]
                                         /\ UNCHANGED <<app_d, app_ask, perm_as, a1, a2>>
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
                                               /\ UNCHANGED <<app_ask, perm_as, a1, a2>>
                                            \/ /\ \/ /\ \E application \in (Applications \ {self}):
                                                          /\ /\ a1' = [a1 EXCEPT ![self] = self]
                                                             /\ a2' = [a2 EXCEPT ![self] = application]
                                                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ask",
                                                                                                      pc        |->  "PLATFORM",
                                                                                                      a1        |->  a1[self],
                                                                                                      a2        |->  a2[self] ] >>
                                                                                                  \o stack[self]]
                                                          /\ pc' = [pc EXCEPT ![self] = "ASK_"]
                                                     /\ UNCHANGED <<app_ask, perm_as>>
                                                  \/ /\ \E p \in Permissions:
                                                          /\ /\ app_ask' = [app_ask EXCEPT ![self] = self]
                                                             /\ perm_as' = [perm_as EXCEPT ![self] = p]
                                                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "askTheUser",
                                                                                                      pc        |->  "PLATFORM",
                                                                                                      app_ask   |->  app_ask[self],
                                                                                                      perm_as   |->  perm_as[self] ] >>
                                                                                                  \o stack[self]]
                                                          /\ pc' = [pc EXCEPT ![self] = "ASK_USER"]
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
                             /\ UNCHANGED << app_d, app_u, app_ask, perm_as, 
                                             a1, a2, app >>
                  /\ UNCHANGED << appCustomPerms, appPerms, CP, cpUserConsent, 
                                  appPermConsents, permsInUse, installed, 
                                  app_a, perm_, a1_, a2_, app_as, perm_a, 
                                  app_m, perm >>

a(self) == PLATFORM(self)

Next == (\E self \in ProcSet:  \/ installApp(self) \/ defineCP(self)
                               \/ arbitraryDecision(self) \/ askUser(self)
                               \/ updateApp(self) \/ askPermission(self)
                               \/ askTheUser(self) \/ ask(self)
                               \/ makeDecision(self) \/ uninstallApp(self))
           \/ (\E self \in Applications: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : /\ WF_vars((pc[self] # "PLATFORM") /\ a(self))
                                      /\ WF_vars(updateApp(self))
                                      /\ WF_vars(uninstallApp(self))
                                      /\ WF_vars(defineCP(self))
                                      /\ WF_vars(ask(self))
                                      /\ WF_vars(askTheUser(self))
                                      /\ WF_vars(installApp(self))
                                      /\ WF_vars(askUser(self))
                                      /\ WF_vars(arbitraryDecision(self))
                                      /\ WF_vars(askPermission(self))
                                      /\ WF_vars(makeDecision(self))

\* END TRANSLATION

TypeOK == /\ appCustomPerms \in [Applications -> [Applications -> PermissionRequestDecision]]
          /\ CP \in [Applications -> CustomPermission]
          /\ cpUserConsent \in [Applications -> [Applications -> UserConsent]]
          /\ installed \in [Applications -> Boolean]
          /\ appPerms \in [Applications -> [Permissions -> PermissionRequestDecision]]
          /\ appPermConsents \in [Applications -> [Permissions -> UserConsent]]
          /\ permsInUse \in [Applications -> [Permissions -> Boolean]]

UserAgreed == [] ~(/\ \E m \in Applications : CP[m] = SENSITIVE \* Li and Tuncay (yes, simultaneously)
                      /\ \E n \in Applications :
                            /\ m # n
                            /\ appCustomPerms[n][m] = GRANT
                            /\ cpUserConsent[n][m] # ALLOW)
                            
UserAgreed2 == [] ~(/\ \E application \in Applications : \E permission \in Permissions : \* Bagheri
                      /\ appPermConsents[application][permission] # ALLOW
                      /\ appPerms[application][permission] = GRANT
                      /\ permsInUse[application][permission] = TRUE)

Authorized == [] ~(/\ \E application \in Applications : \E permission \in Permissions :
                      /\ appPerms[application][permission] # GRANT
                      /\ permsInUse[application][permission] = TRUE)               
=============================================================================
\* Modification History
\* Last modified Mon Mar 20 12:24:30 GMT+03:30 2023 by Amirhosein
