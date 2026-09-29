-- Prove2me | Theorems.Thm_Erdos180_booleanCut_adj
-- name    : Erdos180.booleanCut_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T01:58:49.567171+00:00
-- url     : https://prove2.me/theorems/3b914900-5ec0-4ab4-93a5-64bad11e2554
-- title:
--   Adjacency in a two-colouring cut
-- statement:
--   Given a graph $G$ on $V$ and a two-colouring $c : V \to \{0,1\}$, the cut subgraph
--   retains exactly the bichromatic edges:
--
--   $$u \sim v \text{ in } \mathrm{cut}(G,c) \iff u \sim_G v \ \text{ and } \ c(u) \ne c(v).$$
--
--   The cut construction is the first step of Lemma 3.3 (minimum-degree reduction): a maximum cut
--   yields a bipartite subgraph retaining at least half of the edges of $G$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L66-L70

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open Finset SimpleGraph
open scoped Classical

@[simp]
theorem Erdos180.booleanCut_adj {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) (u v : V) :
    (booleanCut G color).Adj u v ↔ G.Adj u v ∧ color u ≠ color v := by sorry
