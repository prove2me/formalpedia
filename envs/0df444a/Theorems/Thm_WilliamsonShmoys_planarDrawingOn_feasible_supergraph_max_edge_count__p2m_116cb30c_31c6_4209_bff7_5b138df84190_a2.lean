-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_feasible_supergraph_max_edge_count__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
-- name    : WilliamsonShmoys.planarDrawingOn_feasible_supergraph_max_edge_count__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:49.364227+00:00
-- url     : https://prove2.me/theorems/72a88d75-c4c5-4835-9c9d-bd87f2bf6ce8
-- title:
--   Feasible supergraph with maximum edge count
-- statement:
--   Every graph satisfying `P` has a `P` supergraph whose edge count is at least that of the original graph and at least that of every `P` supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_feasible_supergraph_max_edge_count__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hM : P M) :
    ∃ T : SimpleGraph V,
      M.edgeSet.ncard ≤ T.edgeSet.ncard ∧
      M.edgeSet ⊆ T.edgeSet ∧
      P T ∧
      ∀ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet → P U →
        U.edgeSet.ncard ≤ T.edgeSet.ncard := by
  sorry
