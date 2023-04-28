------------------------- MODULE CompositionalSpec -------------------------
EXTENDS Naturals, Sequences

CONSTANT Apps

Boolean == { TRUE, FALSE }

(***

--algorithm System
{
    variables global_var = {};
    
    fair process (module_1 = 1)
         variables var1 = FALSE, var2 = FALSE;
    {
        M1:- while (TRUE)
        {
            var1 := TRUE;
        };
    }
    
    fair process (module_2 = 2)
        variables var1 = FALSE, var2 = FALSE;
    {
        M2:- while (TRUE)
        {
            var1 := TRUE;
        };
    }
}

***)
\* BEGIN TRANSLATION (chksum(pcal) = "86d5f519" /\ chksum(tla) = "42965082")
\* Process variable var1 of process module_1 at line 15 col 20 changed to var1_
\* Process variable var2 of process module_1 at line 15 col 34 changed to var2_
VARIABLES global_var, pc, var1_, var2_, var1, var2

vars == << global_var, pc, var1_, var2_, var1, var2 >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ global_var = {}
        (* Process module_1 *)
        /\ var1_ = FALSE
        /\ var2_ = FALSE
        (* Process module_2 *)
        /\ var1 = FALSE
        /\ var2 = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "M1"
                                        [] self = 2 -> "M2"]

M1 == /\ pc[1] = "M1"
      /\ var1_' = TRUE
      /\ pc' = [pc EXCEPT ![1] = "M1"]
      /\ UNCHANGED << global_var, var2_, var1, var2 >>

module_1 == M1

M2 == /\ pc[2] = "M2"
      /\ var1' = TRUE
      /\ pc' = [pc EXCEPT ![2] = "M2"]
      /\ UNCHANGED << global_var, var1_, var2_, var2 >>

module_2 == M2

Next == module_1 \/ module_2

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars((pc[1] # "M1") /\ module_1)
        /\ WF_vars((pc[2] # "M2") /\ module_2)

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Apr 28 10:15:21 GMT+03:30 2023 by Amirhosein
\* Created Fri Apr 28 08:40:56 GMT+03:30 2023 by Amirhosein
