-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:00:47.865988+00:00
-- url     : https://prove2.me/theorems/5ef2fec7-c68a-4083-8ca2-c9c55a373b08
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex set of size at least three has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
    {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X ≤ W)
    (hV : 3 ≤ Fintype.card V) :
    W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
