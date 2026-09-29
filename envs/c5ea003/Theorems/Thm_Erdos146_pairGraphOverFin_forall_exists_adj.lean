-- Prove2me | Theorems.Thm_Erdos146_pairGraphOverFin_forall_exists_adj
-- name    : Erdos146.pairGraphOverFin_forall_exists_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:53:41.674431+00:00
-- url     : https://prove2.me/theorems/b48b2336-6806-42cd-9f00-10d6e8e7b9c8
-- title:
--   Every vertex of the layered graph has a neighbour
-- statement:
--   Structural fact about the layered graph $H$ of Section 6. The counterexample graph $H$ is built in layers (Section 6): starting from a layer $V_0$ of size $L_0$, each subsequent layer is $V_i = \binom{V_{i-1}}{2}$, and every vertex $\{a,b\} \in V_i$ is joined to its two parents $a, b \in V_{i-1}$. Fact 6.1 records that the result is connected, bipartite and 2-degenerate. Every vertex of the layered graph is adjacent to some other vertex; there are no isolated vertices.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L18019-L18034

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairGraphOverFin_forall_exists_adj
    (baseSize depth : ℕ)
    (hbase : 4 ≤ baseSize)
    (hdepth : 0 < depth) :
    ∀ vertex : Fin (Fintype.card (PairVertex baseSize depth)),
      ∃ neighbor,
        (pairGraphOverFin baseSize depth).Adj vertex neighbor := by sorry
