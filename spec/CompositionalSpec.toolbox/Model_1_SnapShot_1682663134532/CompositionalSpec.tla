------------------------- MODULE CompositionalSpec -------------------------
EXTENDS Naturals, Sequences

CONSTANT Apps

Boolean == { TRUE, FALSE }

(***

--algorithm System
{
    variables
             (*Module1_Component1_Vars*)
             m1_c1_vars = [p \in Apps |-> [var1 |-> FALSE, var2 |-> FALSE]];
             
             (*Module1_Component2_Vars*)
             m1_c2_vars = [p \in Apps |-> FALSE];
             
             (*Module2_Component1_Vars*)
             m2_c1_vars = [p \in Apps |-> FALSE];
    
    fair process (module1 \in Apps)
    {
        PLATFORM:- while (TRUE)
        {
            m1_c1_vars[self].var2 := TRUE;
        };
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "851adc24" /\ chksum(tla) = "b404ea70")
VARIABLES m1_c1_vars, m1_c2_vars, m2_c1_vars, pc

vars == << m1_c1_vars, m1_c2_vars, m2_c1_vars, pc >>

ProcSet == (Apps)

Init == (* Global variables *)
        /\ m1_c1_vars = [p \in Apps |-> [var1 |-> FALSE, var2 |-> FALSE]]
        /\ m1_c2_vars = [p \in Apps |-> FALSE]
        /\ m2_c1_vars = [p \in Apps |-> FALSE]
        /\ pc = [self \in ProcSet |-> "PLATFORM"]

PLATFORM(self) == /\ pc[self] = "PLATFORM"
                  /\ m1_c1_vars' = [m1_c1_vars EXCEPT ![self].var2 = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "PLATFORM"]
                  /\ UNCHANGED << m1_c2_vars, m2_c1_vars >>

module1(self) == PLATFORM(self)

Next == (\E self \in Apps: module1(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Apps : WF_vars((pc[self] # "PLATFORM") /\ module1(self))

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Apr 28 09:55:29 GMT+03:30 2023 by Amirhosein
\* Created Fri Apr 28 08:40:56 GMT+03:30 2023 by Amirhosein
