---- MODULE MC ----
EXTENDS CompositionalSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Apps
const_168266313149414000 == 
{1, 2}
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_168266313149415000 ==
[] ~(\E p \in Apps: m1_c1_vars[p].var2 = TRUE)
----
=============================================================================
\* Modification History
\* Created Fri Apr 28 09:55:31 GMT+03:30 2023 by Amirhosein
