---- MODULE MC ----
EXTENDS CompositionalSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Apps
const_16826628089638000 == 
{1, 2}
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_16826628089639000 ==
\A p \in Apps: m1_c1_vars[p].var1 # TRUE
----
=============================================================================
\* Modification History
\* Created Fri Apr 28 09:50:08 GMT+03:30 2023 by Amirhosein
