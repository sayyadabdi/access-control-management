------------------------- MODULE CompositionalSpec -------------------------
EXTENDS Naturals, Sequences

CONSTANT Apps

Boolean == { TRUE, FALSE }

(***

--algorithm System
{
    variables global_vars = [a |-> {}, b |-> {}];
    
    fair process (module_1 = 1)
         variables component1 = [var1 |-> {}, var2 |-> {}],
                   component2 = [var1 |-> {}, var2 |-> {}];
    {
        M1:- while (TRUE)
        {
            skip;
        };
    }
    
    fair process (module_2 = 2)
        variables component1 = [var1 |-> {}, var2 |-> {}],
                  component2 = [var1 |-> {}, var2 |-> {}];
    {
        M2:- while (TRUE)
        {
            skip;
        };
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "724ec103" /\ chksum(tla) = "fd2e47c1")
\* Process variable component1 of process module_1 at line 15 col 20 changed to component1_
\* Process variable component2 of process module_1 at line 16 col 20 changed to component2_
VARIABLES global_vars, pc, component1_, component2_, component1, component2

vars == << global_vars, pc, component1_, component2_, component1, component2
        >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ global_vars = [a |-> {}, b |-> {}]
        (* Process module_1 *)
        /\ component1_ = [var1 |-> {}, var2 |-> {}]
        /\ component2_ = [var1 |-> {}, var2 |-> {}]
        (* Process module_2 *)
        /\ component1 = [var1 |-> {}, var2 |-> {}]
        /\ component2 = [var1 |-> {}, var2 |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "M1"
                                        [] self = 2 -> "M2"]

M1 == /\ pc[1] = "M1"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "M1"]
      /\ UNCHANGED << global_vars, component1_, component2_, component1, 
                      component2 >>

module_1 == M1

M2 == /\ pc[2] = "M2"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![2] = "M2"]
      /\ UNCHANGED << global_vars, component1_, component2_, component1, 
                      component2 >>

module_2 == M2

Next == module_1 \/ module_2

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars((pc[1] # "M1") /\ module_1)
        /\ WF_vars((pc[2] # "M2") /\ module_2)

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Apr 28 11:04:40 GMT+03:30 2023 by Amirhosein
\* Created Fri Apr 28 08:40:56 GMT+03:30 2023 by Amirhosein
