-- Prove2me | Theorems.Thm_Erdos180_symplecticPointRelated_symm
-- name    : Erdos180.symplecticPointRelated_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:05:21.709315+00:00
-- url     : https://prove2.me/theorems/01c8fffe-9ae1-47a0-8f04-b60945b04533
-- title:
--   The common-neighbour relation is symmetric
-- statement:
--   If $p$ is related to $q$ in the point class of the quadrangle then $q$ is related to $p$.
--
--   For a bipartite graph $B$ with no $C_4$ and no $C_6$ and a bipartition class $S$, the auxiliary *common-neighbour graph* $R_S$ joins $u \ne v$ in $S$ whenever $N_B(u) \cap N_B(v) \ne \emptyset$; one writes $u \sim v$ for adjacency in $R_S$. For an $R_S$-independent triple $T$, $L(T)$ is its set of common centres and $r(T) = |L(T)|$ (§3 of the source). On the quadrangle, $p \sim p'$ means exactly $\langle p, p'\rangle = 0$,
--   which is symmetric because the form is alternating.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1814-L1819

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticPointRelated_symm
    {p q : SymplecticPoint K}
    (h : SymplecticPointRelated K p q) :
    SymplecticPointRelated K q p := by sorry
