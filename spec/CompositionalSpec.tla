------------------------- MODULE CompositionalSpec -------------------------
EXTENDS Naturals, Sequences

CONSTANT Apps

EnvironmentId == 1
ApsId == 2

Boolean == { TRUE, FALSE }

ActionType == { "RecordAudio" }

ConsentType == { "DENIED", "ALLOWED", "ONLY_ONCE", "WHILE_USING_APP" }

DatumType == { "SystemState" }

PermissionType == { "NORMAL", "SIGNATURE", "RUNTIME", "SPECIAL", "URI",
                    "CUSTOM" }

ProtectionLevel == { "NORMAL", "SIGNATURE", "DANGEROUS", "APP_OP" }

(***

--algorithm Universe
{
    variables env_vars = [actions |-> {}, applications |-> {}, data |-> {},
                          permissions |-> {}, permission_groups |-> {}];

              app_vars = [a \in Apps |->
                          [manifest |-> {}, signature |-> {},
                           private_keys |-> {}, public_key |-> {},
                           certificate |-> {}, package |-> {},
                           services |-> {}, receivers |-> {},
                           activities |-> {}, content_providers |-> {}]];

              aps_vars = [permission_history |-> {}];
    
    procedure installApp(app) { INSTALL_APP: return; }
    procedure uninstallApp(app) { UNINSTALL_APP: return; }
    procedure updateApp(app) { UPDATE_APP: return; }
    procedure declarePermission(app) { DECLARE_PERMISSION: return; }
    procedure revokePermission(app) { REVOKE_PERMISSION: return; }
    procedure grantUriPermission(app) { GRANT_URI_PERMISSION: return; }
    procedure revokeUriPermission(app) { REVOKE_URI_PERMISSION: return; }
    procedure checkUriPermission(app) { CHECK_URI_PERMISSION: return; }
    procedure checkSelfPermission(app) { CHECK_SELF_PERMISSION: return; }
    procedure shouldShowRequestPermissionRationale(app) { SHOULD_SHOW_REQUEST_PERMISSION_RATIONALE: return; }
    procedure requestPermission(app) { REQUEST_PERMISSION: return; }
    procedure requestMultiplePermissions(app) { REQUEST_MULTIPLE_PERMISSIONS: return; }
    procedure removeUnusedPermissions(app) { REMOVE_UNUSED_PERMISSIONS: return; }
    
    fair process (EnvNext = EnvironmentId)
        variables i;
    {
        EnvBegin:- while (TRUE)
        {
            skip;
        };
    }
    
    fair process (AppNext \in Apps)
        variables i;
    {
        AppBegin:- while (TRUE)
        {
            skip;
        };
    }
    
    fair process (ApsNext = ApsId)
        variables i;
    {
        ApsBegin:- while (TRUE)
        {
            skip;
        };
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "c250812c" /\ chksum(tla) = "dc3c2faa")
\* Process variable i of process EnvNext at line 53 col 19 changed to i_
\* Process variable i of process AppNext at line 62 col 19 changed to i_A
\* Parameter app of procedure installApp at line 38 col 26 changed to app_
\* Parameter app of procedure uninstallApp at line 39 col 28 changed to app_u
\* Parameter app of procedure updateApp at line 40 col 25 changed to app_up
\* Parameter app of procedure declarePermission at line 41 col 33 changed to app_d
\* Parameter app of procedure revokePermission at line 42 col 32 changed to app_r
\* Parameter app of procedure grantUriPermission at line 43 col 34 changed to app_g
\* Parameter app of procedure revokeUriPermission at line 44 col 35 changed to app_re
\* Parameter app of procedure checkUriPermission at line 45 col 34 changed to app_c
\* Parameter app of procedure checkSelfPermission at line 46 col 35 changed to app_ch
\* Parameter app of procedure shouldShowRequestPermissionRationale at line 47 col 52 changed to app_s
\* Parameter app of procedure requestPermission at line 48 col 33 changed to app_req
\* Parameter app of procedure requestMultiplePermissions at line 49 col 42 changed to app_requ
CONSTANT defaultInitValue
VARIABLES env_vars, app_vars, aps_vars, pc, stack, app_, app_u, app_up, app_d, 
          app_r, app_g, app_re, app_c, app_ch, app_s, app_req, app_requ, app, 
          i_, i_A, i

vars == << env_vars, app_vars, aps_vars, pc, stack, app_, app_u, app_up, 
           app_d, app_r, app_g, app_re, app_c, app_ch, app_s, app_req, 
           app_requ, app, i_, i_A, i >>

ProcSet == {EnvironmentId} \cup (Apps) \cup {ApsId}

Init == (* Global variables *)
        /\ env_vars = [actions |-> {}, applications |-> {}, data |-> {},
                       permissions |-> {}, permission_groups |-> {}]
        /\ app_vars = [a \in Apps |->
                       [manifest |-> {}, signature |-> {},
                        private_keys |-> {}, public_key |-> {},
                        certificate |-> {}, package |-> {},
                        services |-> {}, receivers |-> {},
                        activities |-> {}, content_providers |-> {}]]
        /\ aps_vars = [permission_history |-> {}]
        (* Procedure installApp *)
        /\ app_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure uninstallApp *)
        /\ app_u = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure updateApp *)
        /\ app_up = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure declarePermission *)
        /\ app_d = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure revokePermission *)
        /\ app_r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure grantUriPermission *)
        /\ app_g = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure revokeUriPermission *)
        /\ app_re = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure checkUriPermission *)
        /\ app_c = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure checkSelfPermission *)
        /\ app_ch = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure shouldShowRequestPermissionRationale *)
        /\ app_s = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure requestPermission *)
        /\ app_req = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure requestMultiplePermissions *)
        /\ app_requ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure removeUnusedPermissions *)
        /\ app = [ self \in ProcSet |-> defaultInitValue]
        (* Process EnvNext *)
        /\ i_ = defaultInitValue
        (* Process AppNext *)
        /\ i_A = [self \in Apps |-> defaultInitValue]
        (* Process ApsNext *)
        /\ i = defaultInitValue
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = EnvironmentId -> "EnvBegin"
                                        [] self \in Apps -> "AppBegin"
                                        [] self = ApsId -> "ApsBegin"]

INSTALL_APP(self) == /\ pc[self] = "INSTALL_APP"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << env_vars, app_vars, aps_vars, app_u, 
                                     app_up, app_d, app_r, app_g, app_re, 
                                     app_c, app_ch, app_s, app_req, app_requ, 
                                     app, i_, i_A, i >>

installApp(self) == INSTALL_APP(self)

UNINSTALL_APP(self) == /\ pc[self] = "UNINSTALL_APP"
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app_u' = [app_u EXCEPT ![self] = Head(stack[self]).app_u]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << env_vars, app_vars, aps_vars, app_, 
                                       app_up, app_d, app_r, app_g, app_re, 
                                       app_c, app_ch, app_s, app_req, app_requ, 
                                       app, i_, i_A, i >>

uninstallApp(self) == UNINSTALL_APP(self)

UPDATE_APP(self) == /\ pc[self] = "UPDATE_APP"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_up' = [app_up EXCEPT ![self] = Head(stack[self]).app_up]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << env_vars, app_vars, aps_vars, app_, app_u, 
                                    app_d, app_r, app_g, app_re, app_c, app_ch, 
                                    app_s, app_req, app_requ, app, i_, i_A, i >>

updateApp(self) == UPDATE_APP(self)

DECLARE_PERMISSION(self) == /\ pc[self] = "DECLARE_PERMISSION"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ app_d' = [app_d EXCEPT ![self] = Head(stack[self]).app_d]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << env_vars, app_vars, aps_vars, app_, 
                                            app_u, app_up, app_r, app_g, 
                                            app_re, app_c, app_ch, app_s, 
                                            app_req, app_requ, app, i_, i_A, i >>

declarePermission(self) == DECLARE_PERMISSION(self)

REVOKE_PERMISSION(self) == /\ pc[self] = "REVOKE_PERMISSION"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ app_r' = [app_r EXCEPT ![self] = Head(stack[self]).app_r]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << env_vars, app_vars, aps_vars, app_, 
                                           app_u, app_up, app_d, app_g, app_re, 
                                           app_c, app_ch, app_s, app_req, 
                                           app_requ, app, i_, i_A, i >>

revokePermission(self) == REVOKE_PERMISSION(self)

GRANT_URI_PERMISSION(self) == /\ pc[self] = "GRANT_URI_PERMISSION"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ app_g' = [app_g EXCEPT ![self] = Head(stack[self]).app_g]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                              app_, app_u, app_up, app_d, 
                                              app_r, app_re, app_c, app_ch, 
                                              app_s, app_req, app_requ, app, 
                                              i_, i_A, i >>

grantUriPermission(self) == GRANT_URI_PERMISSION(self)

REVOKE_URI_PERMISSION(self) == /\ pc[self] = "REVOKE_URI_PERMISSION"
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ app_re' = [app_re EXCEPT ![self] = Head(stack[self]).app_re]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                               app_, app_u, app_up, app_d, 
                                               app_r, app_g, app_c, app_ch, 
                                               app_s, app_req, app_requ, app, 
                                               i_, i_A, i >>

revokeUriPermission(self) == REVOKE_URI_PERMISSION(self)

CHECK_URI_PERMISSION(self) == /\ pc[self] = "CHECK_URI_PERMISSION"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ app_c' = [app_c EXCEPT ![self] = Head(stack[self]).app_c]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                              app_, app_u, app_up, app_d, 
                                              app_r, app_g, app_re, app_ch, 
                                              app_s, app_req, app_requ, app, 
                                              i_, i_A, i >>

checkUriPermission(self) == CHECK_URI_PERMISSION(self)

CHECK_SELF_PERMISSION(self) == /\ pc[self] = "CHECK_SELF_PERMISSION"
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ app_ch' = [app_ch EXCEPT ![self] = Head(stack[self]).app_ch]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                               app_, app_u, app_up, app_d, 
                                               app_r, app_g, app_re, app_c, 
                                               app_s, app_req, app_requ, app, 
                                               i_, i_A, i >>

checkSelfPermission(self) == CHECK_SELF_PERMISSION(self)

SHOULD_SHOW_REQUEST_PERMISSION_RATIONALE(self) == /\ pc[self] = "SHOULD_SHOW_REQUEST_PERMISSION_RATIONALE"
                                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                  /\ app_s' = [app_s EXCEPT ![self] = Head(stack[self]).app_s]
                                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                  /\ UNCHANGED << env_vars, 
                                                                  app_vars, 
                                                                  aps_vars, 
                                                                  app_, app_u, 
                                                                  app_up, 
                                                                  app_d, app_r, 
                                                                  app_g, 
                                                                  app_re, 
                                                                  app_c, 
                                                                  app_ch, 
                                                                  app_req, 
                                                                  app_requ, 
                                                                  app, i_, i_A, 
                                                                  i >>

shouldShowRequestPermissionRationale(self) == SHOULD_SHOW_REQUEST_PERMISSION_RATIONALE(self)

REQUEST_PERMISSION(self) == /\ pc[self] = "REQUEST_PERMISSION"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ app_req' = [app_req EXCEPT ![self] = Head(stack[self]).app_req]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << env_vars, app_vars, aps_vars, app_, 
                                            app_u, app_up, app_d, app_r, app_g, 
                                            app_re, app_c, app_ch, app_s, 
                                            app_requ, app, i_, i_A, i >>

requestPermission(self) == REQUEST_PERMISSION(self)

REQUEST_MULTIPLE_PERMISSIONS(self) == /\ pc[self] = "REQUEST_MULTIPLE_PERMISSIONS"
                                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                      /\ app_requ' = [app_requ EXCEPT ![self] = Head(stack[self]).app_requ]
                                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                      /\ UNCHANGED << env_vars, app_vars, 
                                                      aps_vars, app_, app_u, 
                                                      app_up, app_d, app_r, 
                                                      app_g, app_re, app_c, 
                                                      app_ch, app_s, app_req, 
                                                      app, i_, i_A, i >>

requestMultiplePermissions(self) == REQUEST_MULTIPLE_PERMISSIONS(self)

REMOVE_UNUSED_PERMISSIONS(self) == /\ pc[self] = "REMOVE_UNUSED_PERMISSIONS"
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << env_vars, app_vars, 
                                                   aps_vars, app_, app_u, 
                                                   app_up, app_d, app_r, app_g, 
                                                   app_re, app_c, app_ch, 
                                                   app_s, app_req, app_requ, 
                                                   i_, i_A, i >>

removeUnusedPermissions(self) == REMOVE_UNUSED_PERMISSIONS(self)

EnvBegin == /\ pc[EnvironmentId] = "EnvBegin"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![EnvironmentId] = "EnvBegin"]
            /\ UNCHANGED << env_vars, app_vars, aps_vars, stack, app_, app_u, 
                            app_up, app_d, app_r, app_g, app_re, app_c, app_ch, 
                            app_s, app_req, app_requ, app, i_, i_A, i >>

EnvNext == EnvBegin

AppBegin(self) == /\ pc[self] = "AppBegin"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "AppBegin"]
                  /\ UNCHANGED << env_vars, app_vars, aps_vars, stack, app_, 
                                  app_u, app_up, app_d, app_r, app_g, app_re, 
                                  app_c, app_ch, app_s, app_req, app_requ, app, 
                                  i_, i_A, i >>

AppNext(self) == AppBegin(self)

ApsBegin == /\ pc[ApsId] = "ApsBegin"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![ApsId] = "ApsBegin"]
            /\ UNCHANGED << env_vars, app_vars, aps_vars, stack, app_, app_u, 
                            app_up, app_d, app_r, app_g, app_re, app_c, app_ch, 
                            app_s, app_req, app_requ, app, i_, i_A, i >>

ApsNext == ApsBegin

Next == EnvNext \/ ApsNext
           \/ (\E self \in ProcSet:  \/ installApp(self) \/ uninstallApp(self)
                                     \/ updateApp(self) \/ declarePermission(self)
                                     \/ revokePermission(self)
                                     \/ grantUriPermission(self)
                                     \/ revokeUriPermission(self)
                                     \/ checkUriPermission(self)
                                     \/ checkSelfPermission(self)
                                     \/ shouldShowRequestPermissionRationale(self)
                                     \/ requestPermission(self)
                                     \/ requestMultiplePermissions(self)
                                     \/ removeUnusedPermissions(self))
           \/ (\E self \in Apps: AppNext(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars((pc[EnvironmentId] # "EnvBegin") /\ EnvNext)
        /\ \A self \in Apps : WF_vars((pc[self] # "AppBegin") /\ AppNext(self))
        /\ WF_vars((pc[ApsId] # "ApsBegin") /\ ApsNext)

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Mon May 15 06:54:28 GMT+03:30 2023 by Amirhosein
\* Created Fri Apr 28 08:40:56 GMT+03:30 2023 by Amirhosein
