------------ MODULE PermissionManager ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS P, R, A

ASSUME P \in Nat
ASSUME R \in Nat
ASSUME A \in Nat

Permissions == 1..P
Resources == 1..R
Applications == 1..A

Boolean == { "TRUE", "FALSE", "NULL" }
PermissionRequestDecision == { "GRANT", "DENY" }
UserConsent == { "ALLOW", "REJECT" }

(***       this is a comment containing the PlusCal code *

--algorithm PermissionManager
{
    variables appPerms = [i \in Applications |-> [p \in Permissions |-> Boolean]];
              permConstents = [p \in Permissions |-> [a \in Applications |-> Boolean]];
              
    macro arbitraryDecision() {skip;}
    macro askUserPermission() {skip;}
    macro incompleteRevoke() {skip;}
    
    procedure ask() {askLabel: skip;return}
    procedure uninstallApp() {uninstallAppLabel: skip;return}    
    procedure makeDecision() {makeDecisionLabel3: skip;return}
    
    fair process (a \in Applications)
    {
        platform:- while (TRUE)
                   {
                        i1: call ask();
                        i2: call uninstallApp();
                        i3: incompleteRevoke();
                        i4: call makeDecision();
                        i5: askUserPermission();
                        i6: arbitraryDecision();
                   };
    }
}

    this ends the comment containing the PlusCal code
*************)             
\* BEGIN TRANSLATION (chksum(pcal) = "95c8b8da" /\ chksum(tla) = "d41402b0")
VARIABLES appPerms, permConstents, pc, stack

vars == << appPerms, permConstents, pc, stack >>

ProcSet == (Applications)

Init == (* Global variables *)
        /\ appPerms = [i \in Applications |-> [p \in Permissions |-> Boolean]]
        /\ permConstents = [p \in Permissions |-> [a \in Applications |-> Boolean]]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "platform"]

askLabel(self) == /\ pc[self] = "askLabel"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << appPerms, permConstents >>

ask(self) == askLabel(self)

uninstallAppLabel(self) == /\ pc[self] = "uninstallAppLabel"
                           /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ UNCHANGED << appPerms, permConstents >>

uninstallApp(self) == uninstallAppLabel(self)

makeDecisionLabel3(self) == /\ pc[self] = "makeDecisionLabel3"
                            /\ TRUE
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << appPerms, permConstents >>

makeDecision(self) == makeDecisionLabel3(self)

platform(self) == /\ pc[self] = "platform"
                  /\ pc' = [pc EXCEPT ![self] = "i1"]
                  /\ UNCHANGED << appPerms, permConstents, stack >>

i1(self) == /\ pc[self] = "i1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ask",
                                                     pc        |->  "i2" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "askLabel"]
            /\ UNCHANGED << appPerms, permConstents >>

i2(self) == /\ pc[self] = "i2"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "uninstallApp",
                                                     pc        |->  "i3" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "uninstallAppLabel"]
            /\ UNCHANGED << appPerms, permConstents >>

i3(self) == /\ pc[self] = "i3"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "i4"]
            /\ UNCHANGED << appPerms, permConstents, stack >>

i4(self) == /\ pc[self] = "i4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "makeDecision",
                                                     pc        |->  "i5" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "makeDecisionLabel3"]
            /\ UNCHANGED << appPerms, permConstents >>

i5(self) == /\ pc[self] = "i5"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "i6"]
            /\ UNCHANGED << appPerms, permConstents, stack >>

i6(self) == /\ pc[self] = "i6"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "platform"]
            /\ UNCHANGED << appPerms, permConstents, stack >>

a(self) == platform(self) \/ i1(self) \/ i2(self) \/ i3(self) \/ i4(self)
              \/ i5(self) \/ i6(self)

Next == (\E self \in ProcSet:  \/ ask(self) \/ uninstallApp(self)
                               \/ makeDecision(self))
           \/ (\E self \in Applications: a(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Applications : /\ WF_vars((pc[self] # "platform") /\ a(self))
                                      /\ WF_vars(ask(self))
                                      /\ WF_vars(uninstallApp(self))
                                      /\ WF_vars(makeDecision(self))

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu Feb 23 06:14:48 IRST 2023 by Amirhosein
