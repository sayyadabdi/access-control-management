------------------------- MODULE CompositionalSpec -------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT Apps, Permissions

EnvironmentId == "EnvironmentId"
ApsId == "ApsId"
MaxAllowedUpdates == 2

(*** CONSTANTS ***)
Null == "NULL"
PERMISSION_DENIED == "PERMISSION_DENIED"
PERMISSION_ALLOWED == "PERMISSION_ALLOWED"
PERMISSION_ONLY_ONCE == "PERMISSION_ONLY_ONCE"
PERMISSION_WHILE_USING_APP == "PERMISSION_WHILE_USING_APP"
ACTION_RECORD_AUDIO == "ACTION_RECORD_AUDIO"
DATUM_SYSTEM_STATE == "DATUM_SYSTEM_STATE"
PERMISSION_TYPE_URI == "PERMISSION_TYPE_URI"
PERMISSION_TYPE_CUSTOM == "PERMISSION_TYPE_CUSTOM"
PERMISSION_TYPE_NORMAL == "PERMISSION_TYPE_NORMAL"
PERMISSION_TYPE_RUNTIME == "PERMISSION_TYPE_RUNTIME"
PERMISSION_TYPE_SPECIAL == "PERMISSION_TYPE_SPECIAL"
PERMISSION_TYPE_SIGNATURE == "PERMISSION_TYPE_SIGNATURE"
PROTECTION_LEVEL_NORMAL == "PROTECTION_LEVEL_NORMAL"
PROTECTION_LEVEL_APP_OP == "PROTECTION_LEVEL_APP_OP"
PROTECTION_LEVEL_SIGNATURE == "PROTECTION_LEVEL_SIGNATURE"
PROTECTION_LEVEL_DANGEROUS == "PROTECTION_LEVEL_DANGEROUS"
(*** END OF CONSTANTS ***)

(*** ENUMS ***)
Boolean == { TRUE, FALSE, Null }
DatumType == { DATUM_SYSTEM_STATE }
ActionType == { ACTION_RECORD_AUDIO }
ConsentType == { PERMISSION_DENIED, PERMISSION_ALLOWED,
                 PERMISSION_ONLY_ONCE, PERMISSION_WHILE_USING_APP }
ProtectionLevel == { PROTECTION_LEVEL_NORMAL, PROTECTION_LEVEL_SIGNATURE,
                     PROTECTION_LEVEL_DANGEROUS, PROTECTION_LEVEL_APP_OP }
PermissionType == { PERMISSION_TYPE_NORMAL, PERMISSION_TYPE_SIGNATURE,
                    PERMISSION_TYPE_RUNTIME, PERMISSION_TYPE_SPECIAL,
                    PERMISSION_TYPE_URI, PERMISSION_TYPE_CUSTOM }
(*** END OF ENUMS ***)

(***--algorithm Universe
{
    variables env_vars =
    [actions |-> {}, permission_groups |-> {},
     applications |->
      [a \in Apps |-> [installed |-> FALSE, version |-> 0, terminated |-> FALSE]],
       data |-> {}, permissions |-> [p \in Permissions |-> [a \in Apps |-> Null]]];

    app_vars = [a \in Apps |->
                [manifest |-> [p \in Permissions |-> Null],
                 signature |-> {}, private_keys |-> {}, public_key |-> {},
                 certificate |-> {}, package |-> {}, services |-> {},
                 receivers |-> {}, activities |-> {}, content_providers |-> {}]];

    aps_vars = [permission_history |-> {},
                app_permissions |-> [a \in Apps |-> [p \in Permissions |-> Null]]];
                
    permission_type = Null
        
    procedure installApp(app) { INSTALL_APP: env_vars.applications[app].installed := TRUE; return; }
    procedure uninstallApp(app) { UNINSTALL_APP: env_vars.applications[app].installed := FALSE; return; }
    procedure updateApp(app) { UPDATE_APP: env_vars.applications[app].version := env_vars.applications[app].version + 1; return; }
    procedure terminate(app) { TERMINATED: env_vars.applications[self].terminated := TRUE; return; }
    procedure declarePermission(app, perm) { DECLARE_PERMISSION: app_vars[app].manifest[perm] := TRUE; return; }
    procedure revokePermission(app) { REVOKE_PERMISSION: aps_vars.app_permissions[app] := [p \in Permissions |-> Null]; return; }
    procedure requestPermission(app, perm)
    {
     REQUEST_PERMISSION:
     if(aps_vars.app_permissions[app][perm] # Null)
        return;
        
     SWITCH_PERMISSION:
     with(x \in PermissionType)
     {
      permission_type := x;
      
      if(permission_type = PERMISSION_TYPE_NORMAL \/ permission_type = PERMISSION_TYPE_SIGNATURE
         \/ permission_type = PERMISSION_TYPE_SPECIAL)
      {
       \* out of scope
       skip;
      }
      else if(permission_type = PERMISSION_TYPE_RUNTIME \/ permission_type = PERMISSION_TYPE_URI
         \/ permission_type = PERMISSION_TYPE_CUSTOM)
      {
       with(r \in { TRUE, FALSE })
       {
        if(r = TRUE)
         aps_vars.app_permissions[app][perm] := PERMISSION_ALLOWED;
        else
         aps_vars.app_permissions[app][perm] := PERMISSION_DENIED;
       }
      }
     };
     return;
    }
    \*procedure grantUriPermission(app) { GRANT_URI_PERMISSION: return; }
    \*procedure revokeUriPermission(app) { REVOKE_URI_PERMISSION: return; }
    \*procedure checkUriPermission(app) { CHECK_URI_PERMISSION: return; }
    \*procedure checkSelfPermission(app) { CHECK_SELF_PERMISSION: return; }
    \*procedure shouldShowRequestPermissionRationale(app) { SHOULD_SHOW_REQUEST_PERMISSION_RATIONALE: return; }
    \*procedure requestMultiplePermissions(app) { REQUEST_MULTIPLE_PERMISSIONS: return; }
    \*procedure removeUnusedPermissions(app) { REMOVE_UNUSED_PERMISSIONS: return; }
    
    fair process (EnvNext = EnvironmentId)
        variables applications;
    {
        EnvBegin:- while (TRUE)
        {
            either { skip; }
            or
            {
              with (a \in Apps)
              {
               call revokePermission(a);
              }
            }
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
            if(env_vars.applications[self].version < MaxAllowedUpdates)
            {
             call updateApp(self);
            }
           }
          }
          else
          {
           DECLARING_PERMISSION: with (p \in Permissions) { call declarePermission(self, p); };
           INSTALLING_APP: call installApp(self);
          }
         }
        };
    }
    
    fair process (ApsNext = ApsId)
        variables i;
    {
        ApsBegin:- while (TRUE)
        {
         either { skip; }
         or
         {
          with (a \in Apps)
          {
           with (p \in Permissions)
           {
            call requestPermission(a, p);
           }
          }
         }
        };
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "769ce6e9" /\ chksum(tla) = "c9f08f3f")
\* Process variable i of process AppNext at line 124 col 19 changed to i_
\* Parameter app of procedure installApp at line 62 col 26 changed to app_
\* Parameter app of procedure uninstallApp at line 63 col 28 changed to app_u
\* Parameter app of procedure updateApp at line 64 col 25 changed to app_up
\* Parameter app of procedure terminate at line 65 col 25 changed to app_t
\* Parameter app of procedure declarePermission at line 66 col 33 changed to app_d
\* Parameter perm of procedure declarePermission at line 66 col 38 changed to perm_
\* Parameter app of procedure revokePermission at line 67 col 32 changed to app_r
CONSTANT defaultInitValue
VARIABLES env_vars, app_vars, aps_vars, permission_type, pc, stack, app_, 
          app_u, app_up, app_t, app_d, perm_, app_r, app, perm, applications, 
          i_, i

vars == << env_vars, app_vars, aps_vars, permission_type, pc, stack, app_, 
           app_u, app_up, app_t, app_d, perm_, app_r, app, perm, applications, 
           i_, i >>

ProcSet == {EnvironmentId} \cup (Apps) \cup {ApsId}

Init == (* Global variables *)
        /\ env_vars = [actions |-> {}, permission_groups |-> {},
                       applications |->
                        [a \in Apps |-> [installed |-> FALSE, version |-> 0, terminated |-> FALSE]],
                         data |-> {}, permissions |-> [p \in Permissions |-> [a \in Apps |-> Null]]]
        /\ app_vars = [a \in Apps |->
                       [manifest |-> [p \in Permissions |-> Null],
                        signature |-> {}, private_keys |-> {}, public_key |-> {},
                        certificate |-> {}, package |-> {}, services |-> {},
                        receivers |-> {}, activities |-> {}, content_providers |-> {}]]
        /\ aps_vars = [permission_history |-> {},
                       app_permissions |-> [a \in Apps |-> [p \in Permissions |-> Null]]]
        /\ permission_type = Null
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
        /\ perm_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure revokePermission *)
        /\ app_r = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure requestPermission *)
        /\ app = [ self \in ProcSet |-> defaultInitValue]
        /\ perm = [ self \in ProcSet |-> defaultInitValue]
        (* Process EnvNext *)
        /\ applications = defaultInitValue
        (* Process AppNext *)
        /\ i_ = [self \in Apps |-> defaultInitValue]
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
                     /\ UNCHANGED << app_vars, aps_vars, permission_type, 
                                     app_u, app_up, app_t, app_d, perm_, app_r, 
                                     app, perm, applications, i_, i >>

installApp(self) == INSTALL_APP(self)

UNINSTALL_APP(self) == /\ pc[self] = "UNINSTALL_APP"
                       /\ env_vars' = [env_vars EXCEPT !.applications[app_u[self]].installed = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ app_u' = [app_u EXCEPT ![self] = Head(stack[self]).app_u]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << app_vars, aps_vars, permission_type, 
                                       app_, app_up, app_t, app_d, perm_, 
                                       app_r, app, perm, applications, i_, i >>

uninstallApp(self) == UNINSTALL_APP(self)

UPDATE_APP(self) == /\ pc[self] = "UPDATE_APP"
                    /\ env_vars' = [env_vars EXCEPT !.applications[app_up[self]].version = env_vars.applications[app_up[self]].version + 1]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_up' = [app_up EXCEPT ![self] = Head(stack[self]).app_up]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << app_vars, aps_vars, permission_type, app_, 
                                    app_u, app_t, app_d, perm_, app_r, app, 
                                    perm, applications, i_, i >>

updateApp(self) == UPDATE_APP(self)

TERMINATED(self) == /\ pc[self] = "TERMINATED"
                    /\ env_vars' = [env_vars EXCEPT !.applications[self].terminated = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ app_t' = [app_t EXCEPT ![self] = Head(stack[self]).app_t]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << app_vars, aps_vars, permission_type, app_, 
                                    app_u, app_up, app_d, perm_, app_r, app, 
                                    perm, applications, i_, i >>

terminate(self) == TERMINATED(self)

DECLARE_PERMISSION(self) == /\ pc[self] = "DECLARE_PERMISSION"
                            /\ app_vars' = [app_vars EXCEPT ![app_d[self]].manifest[perm_[self]] = TRUE]
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ app_d' = [app_d EXCEPT ![self] = Head(stack[self]).app_d]
                            /\ perm_' = [perm_ EXCEPT ![self] = Head(stack[self]).perm_]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << env_vars, aps_vars, 
                                            permission_type, app_, app_u, 
                                            app_up, app_t, app_r, app, perm, 
                                            applications, i_, i >>

declarePermission(self) == DECLARE_PERMISSION(self)

REVOKE_PERMISSION(self) == /\ pc[self] = "REVOKE_PERMISSION"
                           /\ aps_vars' = [aps_vars EXCEPT !.app_permissions[app_r[self]] = [p \in Permissions |-> Null]]
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ app_r' = [app_r EXCEPT ![self] = Head(stack[self]).app_r]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << env_vars, app_vars, permission_type, 
                                           app_, app_u, app_up, app_t, app_d, 
                                           perm_, app, perm, applications, i_, 
                                           i >>

revokePermission(self) == REVOKE_PERMISSION(self)

REQUEST_PERMISSION(self) == /\ pc[self] = "REQUEST_PERMISSION"
                            /\ IF aps_vars.app_permissions[app[self]][perm[self]] # Null
                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                                       /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "SWITCH_PERMISSION"]
                                       /\ UNCHANGED << stack, app, perm >>
                            /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                            permission_type, app_, app_u, 
                                            app_up, app_t, app_d, perm_, app_r, 
                                            applications, i_, i >>

SWITCH_PERMISSION(self) == /\ pc[self] = "SWITCH_PERMISSION"
                           /\ \E x \in PermissionType:
                                /\ permission_type' = x
                                /\ IF permission_type' = PERMISSION_TYPE_NORMAL \/ permission_type' = PERMISSION_TYPE_SIGNATURE
                                      \/ permission_type' = PERMISSION_TYPE_SPECIAL
                                      THEN /\ TRUE
                                           /\ UNCHANGED aps_vars
                                      ELSE /\ IF      permission_type' = PERMISSION_TYPE_RUNTIME \/ permission_type' = PERMISSION_TYPE_URI
                                                 \/ permission_type' = PERMISSION_TYPE_CUSTOM
                                                 THEN /\ \E r \in { TRUE, FALSE }:
                                                           IF r = TRUE
                                                              THEN /\ aps_vars' = [aps_vars EXCEPT !.app_permissions[app[self]][perm[self]] = PERMISSION_ALLOWED]
                                                              ELSE /\ aps_vars' = [aps_vars EXCEPT !.app_permissions[app[self]][perm[self]] = PERMISSION_DENIED]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED aps_vars
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ app' = [app EXCEPT ![self] = Head(stack[self]).app]
                           /\ perm' = [perm EXCEPT ![self] = Head(stack[self]).perm]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << env_vars, app_vars, app_, app_u, 
                                           app_up, app_t, app_d, perm_, app_r, 
                                           applications, i_, i >>

requestPermission(self) == REQUEST_PERMISSION(self)
                              \/ SWITCH_PERMISSION(self)

EnvBegin == /\ pc[EnvironmentId] = "EnvBegin"
            /\ \/ /\ TRUE
                  /\ pc' = [pc EXCEPT ![EnvironmentId] = "EnvBegin"]
                  /\ UNCHANGED <<stack, app_r>>
               \/ /\ \E a \in Apps:
                       /\ /\ app_r' = [app_r EXCEPT ![EnvironmentId] = a]
                          /\ stack' = [stack EXCEPT ![EnvironmentId] = << [ procedure |->  "revokePermission",
                                                                            pc        |->  "EnvBegin",
                                                                            app_r     |->  app_r[EnvironmentId] ] >>
                                                                        \o stack[EnvironmentId]]
                       /\ pc' = [pc EXCEPT ![EnvironmentId] = "REVOKE_PERMISSION"]
            /\ UNCHANGED << env_vars, app_vars, aps_vars, permission_type, 
                            app_, app_u, app_up, app_t, app_d, perm_, app, 
                            perm, applications, i_, i >>

EnvNext == EnvBegin

AppBegin(self) == /\ pc[self] = "AppBegin"
                  /\ IF env_vars.applications[self].terminated # TRUE
                        THEN /\ \/ /\ /\ app_t' = [app_t EXCEPT ![self] = self]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "terminate",
                                                                               pc        |->  "AppBegin",
                                                                               app_t     |->  app_t[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "TERMINATED"]
                                   /\ UNCHANGED <<app_u, app_up>>
                                \/ /\ IF env_vars.applications[self].installed = TRUE
                                         THEN /\ \/ /\ /\ app_u' = [app_u EXCEPT ![self] = self]
                                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                                                                pc        |->  "AppBegin",
                                                                                                app_u     |->  app_u[self] ] >>
                                                                                            \o stack[self]]
                                                    /\ pc' = [pc EXCEPT ![self] = "UNINSTALL_APP"]
                                                    /\ UNCHANGED app_up
                                                 \/ /\ IF env_vars.applications[self].version < MaxAllowedUpdates
                                                          THEN /\ /\ app_up' = [app_up EXCEPT ![self] = self]
                                                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "updateApp",
                                                                                                           pc        |->  "AppBegin",
                                                                                                           app_up    |->  app_up[self] ] >>
                                                                                                       \o stack[self]]
                                                               /\ pc' = [pc EXCEPT ![self] = "UPDATE_APP"]
                                                          ELSE /\ pc' = [pc EXCEPT ![self] = "AppBegin"]
                                                               /\ UNCHANGED << stack, 
                                                                               app_up >>
                                                    /\ app_u' = app_u
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "DECLARING_PERMISSION"]
                                              /\ UNCHANGED << stack, app_u, 
                                                              app_up >>
                                   /\ app_t' = app_t
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                             /\ UNCHANGED << stack, app_u, app_up, app_t >>
                  /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                  permission_type, app_, app_d, perm_, app_r, 
                                  app, perm, applications, i_, i >>

DECLARING_PERMISSION(self) == /\ pc[self] = "DECLARING_PERMISSION"
                              /\ \E p \in Permissions:
                                   /\ /\ app_d' = [app_d EXCEPT ![self] = self]
                                      /\ perm_' = [perm_ EXCEPT ![self] = p]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "declarePermission",
                                                                               pc        |->  "INSTALLING_APP",
                                                                               app_d     |->  app_d[self],
                                                                               perm_     |->  perm_[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "DECLARE_PERMISSION"]
                              /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                              permission_type, app_, app_u, 
                                              app_up, app_t, app_r, app, perm, 
                                              applications, i_, i >>

INSTALLING_APP(self) == /\ pc[self] = "INSTALLING_APP"
                        /\ /\ app_' = [app_ EXCEPT ![self] = self]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "installApp",
                                                                    pc        |->  "AppBegin",
                                                                    app_      |->  app_[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "INSTALL_APP"]
                        /\ UNCHANGED << env_vars, app_vars, aps_vars, 
                                        permission_type, app_u, app_up, app_t, 
                                        app_d, perm_, app_r, app, perm, 
                                        applications, i_, i >>

AppNext(self) == AppBegin(self) \/ DECLARING_PERMISSION(self)
                    \/ INSTALLING_APP(self)

ApsBegin == /\ pc[ApsId] = "ApsBegin"
            /\ \/ /\ TRUE
                  /\ pc' = [pc EXCEPT ![ApsId] = "ApsBegin"]
                  /\ UNCHANGED <<stack, app, perm>>
               \/ /\ \E a \in Apps:
                       \E p \in Permissions:
                         /\ /\ app' = [app EXCEPT ![ApsId] = a]
                            /\ perm' = [perm EXCEPT ![ApsId] = p]
                            /\ stack' = [stack EXCEPT ![ApsId] = << [ procedure |->  "requestPermission",
                                                                      pc        |->  "ApsBegin",
                                                                      app       |->  app[ApsId],
                                                                      perm      |->  perm[ApsId] ] >>
                                                                  \o stack[ApsId]]
                         /\ pc' = [pc EXCEPT ![ApsId] = "REQUEST_PERMISSION"]
            /\ UNCHANGED << env_vars, app_vars, aps_vars, permission_type, 
                            app_, app_u, app_up, app_t, app_d, perm_, app_r, 
                            applications, i_, i >>

ApsNext == ApsBegin

Next == EnvNext \/ ApsNext
           \/ (\E self \in ProcSet:  \/ installApp(self) \/ uninstallApp(self)
                                     \/ updateApp(self) \/ terminate(self)
                                     \/ declarePermission(self)
                                     \/ revokePermission(self)
                                     \/ requestPermission(self))
           \/ (\E self \in Apps: AppNext(self))

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars((pc[EnvironmentId] # "EnvBegin") /\ EnvNext)
           /\ WF_vars(revokePermission(EnvironmentId))
        /\ \A self \in Apps : /\ WF_vars((pc[self] # "AppBegin") /\ AppNext(self))
                              /\ WF_vars(terminate(self))
                              /\ WF_vars(uninstallApp(self))
                              /\ WF_vars(updateApp(self))
                              /\ WF_vars(declarePermission(self))
                              /\ WF_vars(installApp(self))
        /\ /\ WF_vars((pc[ApsId] # "ApsBegin") /\ ApsNext)
           /\ WF_vars(requestPermission(ApsId))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat May 27 09:44:39 GMT+03:30 2023 by Amirhosein
\* Created Fri Apr 28 08:40:56 GMT+03:30 2023 by Amirhosein
