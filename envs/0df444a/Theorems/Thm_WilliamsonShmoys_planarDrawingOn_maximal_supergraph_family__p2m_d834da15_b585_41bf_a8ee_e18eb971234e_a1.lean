-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximal_supergraph_family__p2m_d834da15_b585_41bf_a8ee_e18eb971234e_a1
-- name    : WilliamsonShmoys.planarDrawingOn_maximal_supergraph_family__p2m_d834da15_b585_41bf_a8ee_e18eb971234e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:32.174663+00:00
-- url     : https://prove2.me/theorems/116cb30c-31c6-4209-bff7-5b138df84190
-- title:
--   Maximal element in a finite family of graph supergraphs
-- statement:
--   For any property P on graphs over a finite ordered vertex type, every graph M satisfying P has a P supergraph whose edge set is maximal among P supergraphs of M. Its edge count is at least M's.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_maximal_supergraph_family__p2m_d834da15_b585_41bf_a8ee_e18eb971234e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hM : P M) :
    ∃ T : SimpleGraph V,
      M.edgeSet.ncard ≤ T.edgeSet.ncard ∧
      M.edgeSet ⊆ T.edgeSet ∧
      P T ∧
      ∀ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet → P U →
        U.edgeSet ⊆ T.edgeSet := by
  sorry
