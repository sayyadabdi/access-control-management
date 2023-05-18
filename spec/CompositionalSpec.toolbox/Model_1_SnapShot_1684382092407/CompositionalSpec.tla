------------------------- MODULE CompositionalSpec -------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT Apps, Permissions

EnvironmentId == "EnvironmentId"
ApsId == "ApsId"
MaxAllowedUpdates == 2

Null == "NULL"
Boolean == { TRUE, FALSE, Null }

RecordAudio == "RecordAudio"
ActionType == { RecordAudio }

DENIED == "DENIED"
ALLOWED == "ALLOWED"
ONLY_ONCE == "ONLY_ONCE"
WHILE_USING_APP == "WHILE_USING_APP"
ConsentType == { DENIED, ALLOWED, ONLY_ONCE, WHILE_USING_APP }

SystemState == "SystemState"
DatumType == { SystemState }

PERMISSION_TYPE_NORMAL == "NORMAL"
PERMISSION_TYPE_SIGNATURE == "SIGNATURE"
PERMISSION_TYPE_RUNTIME == "RUNTIME"
PERMISSION_TYPE_SPECIAL == "SPECIAL"
PERMISSION_TYPE_URI == "URI"
PERMISSION_TYPE_CUSTOM == "CUSTOM"
PermissionType == { PERMISSION_TYPE_NORMAL, PERMISSION_TYPE_SIGNATURE, PERMISSION_TYPE_RUNTIME, PERMISSION_TYPE_SPECIAL, PERMISSION_TYPE_URI,
                    PERMISSION_TYPE_CUSTOM }

PROTECTION_LEVEL_NORMAL == "NORMAL"
PROTECTION_LEVEL_SIGNATURE == "SIGNATURE"
PROTECTION_LEVEL_DANGEROUS == "DANGEROUS"
PROTECTION_LEVEL_APP_OP == "APP_OP"
ProtectionLevel == { PROTECTION_LEVEL_NORMAL, PROTECTION_LEVEL_SIGNATURE, PROTECTION_LEVEL_DANGEROUS, PROTECTION_LEVEL_APP_OP }

(***--algorithm Universe
{
    variables env_vars = [actions |-> {}, applications |-> [a \in Apps |-> [installed |-> FALSE, version |-> 0, terminated |-> FALSE]], data |-> {},
                          permissions |-> [p \in Permissions |-> [a \in Apps |-> Null]], permission_groups |-> {}];

              app_vars = [a \in Apps |->
                          [manifest |-> [p \in Permissions |-> Null], signature |-> {},
                           private_keys |-> {}, public_key |-> {},
                           certificate |-> {}, package |-> {},
                           services |-> {}, receivers |-> {},
                           activities |-> {}, content_providers |-> {}]];

              aps_vars = [permission_history |-> {}];
    
    procedure installApp(app) { INSTALL_APP: env_vars.applications[app].installed := TRUE; return; }
    procedure uninstallApp(app) { UNINSTALL_APP: env_vars.applications[app].installed := FALSE; return; }
    procedure updateApp(app) { UPDATE_APP: env_vars.applications[app].version := env_vars.applications[app].version + 1; return; }
    procedure terminate(app) { TERMINATED: env_vars.applications[self].terminated := TRUE; return; }
    procedure declarePermission(app, perm) { DECLARE_PERMISSION: app_vars[app].manifest[perm] := TRUE; return; }
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
        EnvBegin:- while (FALSE)
        {
            skip;
        };
    }
    
    fair process (AppNext \in Apps)
        variables i;
    {
        AppBegin:- while (env_vars.applications[self].terminated # TRUE)
        {
         either
         {
          call terminate(self);
         }
         or
         {
          if(env_vars.applications[self].installed = TRUE)
          {
           either
           {
             call uninstallApp(self);
           }
           or
           {
            either
            {
             if(env_vars.applications[self].version < MaxAllowedUpdates)
             {
              call updateApp(self);
             }
            }
            or
            {
             with (p \in Permissions) { call declarePermission(self, p); }
            }
           }
          }
          else
          {
           call installApp(self);
          }
         }
        };
    }
    
    fair process (ApsNext = ApsId)
        variables i;
    {
        ApsBegin:- while (FALSE)
        {
            skip;
        };
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "111b37a4" /\ chksum(tla) = "3d2c0a9d")
\* Process variable i of process EnvNext at line 70 col 19 changed to i_
\* Process variable i of process AppNext at line 79 col 19 changed to i_A
\* Parameter app of procedure installApp at line 54 col 26 changed to app_
\* Parameter app of procedure uninstallApp at line 55 col 28 changed to app_u
\* Parameter app of procedure updateApp at line 56 col 25 changed to app_up
\* Parameter app of procedure terminate at line 57 col 25 changed to app_t
\* Parameter app of procedure declarePermission at line 58 col 33 changed to app_d
\* Parameter app of procedure revokePermission at line 59 col 32 changed to app_r
\* Parameter app of procedure grantUriPermission at line 60 col 34 changed to app_g
\* Parameter app of procedure revokeUriPermission at line 61 col 35 changed to app_re
\* Parameter app of procedure checkUriPermission at line 62 col 34 changed to app_c
\* Parameter app of procedure checkSelfPermission at line 63 col 35 changed to app_ch
\* Parameter app of procedure shouldShowRequestPermissionRationale at line 64 col 52 changed to app_s
\* Parameter app of procedure requestPermission at line 65 col 33 changed to app_req
\* Parameter app of procedure requestMultiplePermissions at line 66 col 42 changed to app_requ
CONSTANT defaultInitValue
VARIABLES env_vars, app_vars, aps_vars, pc, stack, app_, app_u, app_up, app_t, 
          app_d, perm, app_r, app_g, app_re, app_c, app_ch, app_s, app_req, 
          app_requ, app, i_, i_A, i

vars == << env_vars, app_vars, aps_vars, pc, stack, app_, app_u, app_up, 
           app_t, app_d, perm, app_r, app_g, app_re, app_c, app_ch, app_s, 
           app_req, app_requ, app, i_, i_A, i >>

ProcSet == {EnvironmentId} \cup (Apps) \cup {ApsId}

Init == (* Global variables *)
        /\ env_vars = [actions |-> {}, applications |-> [a \in Apps |-> [installed |-> FALSE, version |-> 0, terminated |-> FALSE]], data |-> {},
                       permissions |-> [p \in Permissions |-> [a \in Apps |-> Null]], permission_groups |-> {}]
        /\ app_vars = [a \in Apps |->
                       [manifest |-> [p \in Permissions |-> Null], signature |-> {},
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
        (* Procedure terminate *)
        /\ app_t = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure declarePermission *)
        /\ app_d = [ self \in ProcSet |-> defaultInitValue]
        /\ perm = [ self \in ProcSet |-> defaultInitValue]
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
                     /\ env_vars' = [env_vars EXCEPT !.applications[app_[self]].installed = TRUE]
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ app_' = [app_ EXCEPT ![self] = Head(stack[self]).app_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << app_vars, aps_vars, app_u, app_up, app_t, 
                                     app_d, perm, app_r, app_g, app_re, app_c, 
                                     app_ch, app_s, app_req, app_requ, app, i_, 
                                     i_A, i >>

installApp(self) == INSTALL_APP(self)

UNINSTALL_APP(self) == /\ pc[self] = "UNINSTALL_APP"
                       /\ env_vars' = [env_vars EXCEPT !.applications[app_u[self]].installed = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app_u' = [app_u EXCEPT ![self] = Head(stack[self]).app_u]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << app_vars, aps_vars, app_, app_up, app_t, 
                                       app_d, perm, app_r, app_g, app_re, 
                                       app_c, app_ch, app_s, app_req, app_requ, 
                                       app, i_, i_A, i >>

uninstallApp(self) == UNINSTALL_APP(self)

UPDATE_APP(self) == /\ pc[self] = "UPDATE_APP"
                    /\ env_vars' = [env_vars EXCEPT !.applications[app_up[self]].version = env_vars.applications[app_up[self]].version + 1]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_up' = [app_up EXCEPT ![self] = Head(stack[self]).app_up]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << app_vars, aps_vars, app_, app_u, app_t, 
                                    app_d, perm, app_r, app_g, app_re, app_c, 
                                    app_ch, app_s, app_req, app_requ, app, i_, 
                                    i_A, i >>

updateApp(self) == UPDATE_APP(self)

TERMINATED(self) == /\ pc[self] = "TERMINATED"
                    /\ env_vars' = [env_vars EXCEPT !.applications[self].terminated = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_t' = [app_t EXCEPT ![self] = Head(stack[self]).app_t]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << app_vars, aps_vars, app_, app_u, app_up, 
                                    app_d, perm, app_r, app_g, app_re, app_c, 
                                    app_ch, app_s, app_req, app_requ, app, i_, 
                                    i_A, i >>

terminate(self) == TERMINATED(self)

DECLARE_PERMISSION(self) == /\ pc[self] = "DECLARE_PERMISSION"
                            /\ app_vars' = [app_vars EXCEPT ![app_d[self]].manifest[perm[self]] = TRUE]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ app_d' = [app_d EXCEPT ![self] = Head(stack[self]).app_d]
                            /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << env_vars, aps_vars, app_, app_u, 
                                            app_up, app_t, app_r, app_g, 
                                            app_re, app_c, app_ch, app_s, 
                                            app_req, app_requ, app, i_, i_A, i >>

declarePermission(self) == DECLARE_PERMISSION(self)

REVOKE_PERMISSION(self) == /\ pc[self] = "REVOKE_PERMISSION"
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ app_r' = [app_r EXCEPT ![self] = Head(stack[self]).app_r]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << env_vars, app_vars, aps_vars, app_, 
                                           app_u, app_up, app_t, app_d, perm, 
                                           app_g, app_re, app_c, app_ch, app_s, 
                                           app_req, app_requ, app, i_, i_A, i >>

revokePermission(self) == REVOKE_PERMISSION(self)

GRANT_URI_PERMISSION(self) == /\ pc[self] = "GRANT_URI_PERMISSION"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ app_g' = [app_g EXCEPT ![self] = Head(stack[self]).app_g]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                              app_, app_u, app_up, app_t, 
                                              app_d, perm, app_r, app_re, 
                                              app_c, app_ch, app_s, app_req, 
                                              app_requ, app, i_, i_A, i >>

grantUriPermission(self) == GRANT_URI_PERMISSION(self)

REVOKE_URI_PERMISSION(self) == /\ pc[self] = "REVOKE_URI_PERMISSION"
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ app_re' = [app_re EXCEPT ![self] = Head(stack[self]).app_re]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                               app_, app_u, app_up, app_t, 
                                               app_d, perm, app_r, app_g, 
                                               app_c, app_ch, app_s, app_req, 
                                               app_requ, app, i_, i_A, i >>

revokeUriPermission(self) == REVOKE_URI_PERMISSION(self)

CHECK_URI_PERMISSION(self) == /\ pc[self] = "CHECK_URI_PERMISSION"
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ app_c' = [app_c EXCEPT ![self] = Head(stack[self]).app_c]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                              app_, app_u, app_up, app_t, 
                                              app_d, perm, app_r, app_g, 
                                              app_re, app_ch, app_s, app_req, 
                                              app_requ, app, i_, i_A, i >>

checkUriPermission(self) == CHECK_URI_PERMISSION(self)

CHECK_SELF_PERMISSION(self) == /\ pc[self] = "CHECK_SELF_PERMISSION"
                               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                               /\ app_ch' = [app_ch EXCEPT ![self] = Head(stack[self]).app_ch]
                               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                               app_, app_u, app_up, app_t, 
                                               app_d, perm, app_r, app_g, 
                                               app_re, app_c, app_s, app_req, 
                                               app_requ, app, i_, i_A, i >>

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
                                                                  app_t, app_d, 
                                                                  perm, app_r, 
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
                                            app_u, app_up, app_t, app_d, perm, 
                                            app_r, app_g, app_re, app_c, 
                                            app_ch, app_s, app_requ, app, i_, 
                                            i_A, i >>

requestPermission(self) == REQUEST_PERMISSION(self)

REQUEST_MULTIPLE_PERMISSIONS(self) == /\ pc[self] = "REQUEST_MULTIPLE_PERMISSIONS"
                                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                      /\ app_requ' = [app_requ EXCEPT ![self] = Head(stack[self]).app_requ]
                                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                      /\ UNCHANGED << env_vars, app_vars, 
                                                      aps_vars, app_, app_u, 
                                                      app_up, app_t, app_d, 
                                                      perm, app_r, app_g, 
                                                      app_re, app_c, app_ch, 
                                                      app_s, app_req, app, i_, 
                                                      i_A, i >>

requestMultiplePermissions(self) == REQUEST_MULTIPLE_PERMISSIONS(self)

REMOVE_UNUSED_PERMISSIONS(self) == /\ pc[self] = "REMOVE_UNUSED_PERMISSIONS"
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << env_vars, app_vars, 
                                                   aps_vars, app_, app_u, 
                                                   app_up, app_t, app_d, perm, 
                                                   app_r, app_g, app_re, app_c, 
                                                   app_ch, app_s, app_req, 
                                                   app_requ, i_, i_A, i >>

removeUnusedPermissions(self) == REMOVE_UNUSED_PERMISSIONS(self)

EnvBegin == /\ pc[EnvironmentId] = "EnvBegin"
            /\ IF FALSE
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![EnvironmentId] = "EnvBegin"]
                  ELSE /\ pc' = [pc EXCEPT ![EnvironmentId] = "Done"]
            /\ UNCHANGED << env_vars, app_vars, aps_vars, stack, app_, app_u, 
                            app_up, app_t, app_d, perm, app_r, app_g, app_re, 
                            app_c, app_ch, app_s, app_req, app_requ, app, i_, 
                            i_A, i >>

EnvNext == EnvBegin

AppBegin(self) == /\ pc[self] = "AppBegin"
                  /\ IF env_vars.applications[self].terminated # TRUE
                        THEN /\ \/ /\ /\ app_t' = [app_t EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "terminate",
                                                                               pc        |->  "AppBegin",
                                                                               app_t     |->  app_t[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "TERMINATED"]
                                   /\ UNCHANGED <<app_, app_u, app_up, app_d, perm>>
                                \/ /\ IF env_vars.applications[self].installed = TRUE
                                         THEN /\ \/ /\ /\ app_u' = [app_u EXCEPT ![self] = self]
                                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                                                pc        |->  "AppBegin",
                                                                                                app_u     |->  app_u[self] ] >>
                                                                                            \o stack[self]]
                                                    /\ pc' = [pc EXCEPT ![self] = "UNINSTALL_APP"]
                                                    /\ UNCHANGED <<app_up, app_d, perm>>
                                                 \/ /\ \/ /\ IF env_vars.applications[self].version < MaxAllowedUpdates
                                                                THEN /\ /\ app_up' = [app_up EXCEPT ![self] = self]
                                                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateApp",
                                                                                                                 pc        |->  "AppBegin",
                                                                                                                 app_up    |->  app_up[self] ] >>
                                                                                                             \o stack[self]]
                                                                     /\ pc' = [pc EXCEPT ![self] = "UPDATE_APP"]
                                                                ELSE /\ pc' = [pc EXCEPT ![self] = "AppBegin"]
                                                                     /\ UNCHANGED << stack, 
                                                                                     app_up >>
                                                          /\ UNCHANGED <<app_d, perm>>
                                                       \/ /\ \E p \in Permissions:
                                                               /\ /\ app_d' = [app_d EXCEPT ![self] = self]
                                                                  /\ perm' = [perm EXCEPT ![self] = p]
                                                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "declarePermission",
                                                                                                           pc        |->  "AppBegin",
                                                                                                           app_d     |->  app_d[self],
                                                                                                           perm      |->  perm[self] ] >>
                                                                                                       \o stack[self]]
                                                               /\ pc' = [pc EXCEPT ![self] = "DECLARE_PERMISSION"]
                                                          /\ UNCHANGED app_up
                                                    /\ app_u' = app_u
                                              /\ app_' = app_
                                         ELSE /\ /\ app_' = [app_ EXCEPT ![self] = self]
                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "installApp",
                                                                                          pc        |->  "AppBegin",
                                                                                          app_      |->  app_[self] ] >>
                                                                                      \o stack[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "INSTALL_APP"]
                                              /\ UNCHANGED << app_u, app_up, 
                                                              app_d, perm >>
                                   /\ app_t' = app_t
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << stack, app_, app_u, app_up, app_t, 
                                             app_d, perm >>
                  /\ UNCHANGED << env_vars, app_vars, aps_vars, app_r, app_g, 
                                  app_re, app_c, app_ch, app_s, app_req, 
                                  app_requ, app, i_, i_A, i >>

AppNext(self) == AppBegin(self)

ApsBegin == /\ pc[ApsId] = "ApsBegin"
            /\ IF FALSE
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![ApsId] = "ApsBegin"]
                  ELSE /\ pc' = [pc EXCEPT ![ApsId] = "Done"]
            /\ UNCHANGED << env_vars, app_vars, aps_vars, stack, app_, app_u, 
                            app_up, app_t, app_d, perm, app_r, app_g, app_re, 
                            app_c, app_ch, app_s, app_req, app_requ, app, i_, 
                            i_A, i >>

ApsNext == ApsBegin

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == EnvNext \/ ApsNext
           \/ (\E self \in ProcSet:  \/ installApp(self) \/ uninstallApp(self)
                                     \/ updateApp(self) \/ terminate(self)
                                     \/ declarePermission(self)
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
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars((pc[EnvironmentId] # "EnvBegin") /\ EnvNext)
        /\ \A self \in Apps : /\ WF_vars((pc[self] # "AppBegin") /\ AppNext(self))
                              /\ WF_vars(terminate(self))
                              /\ WF_vars(uninstallApp(self))
                              /\ WF_vars(updateApp(self))
                              /\ WF_vars(declarePermission(self))
                              /\ WF_vars(installApp(self))
        /\ WF_vars((pc[ApsId] # "ApsBegin") /\ ApsNext)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu May 18 07:23:01 GMT+03:30 2023 by Amirhosein
\* Created Fri Apr 28 08:40:56 GMT+03:30 2023 by Amirhosein
