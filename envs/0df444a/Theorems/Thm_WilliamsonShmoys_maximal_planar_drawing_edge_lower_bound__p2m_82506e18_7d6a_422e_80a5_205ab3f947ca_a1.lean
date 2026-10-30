-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:30.882755+00:00
-- url     : https://prove2.me/theorems/e780fef6-809e-4537-b9f8-0f8e159d28fc
-- title:
--   Lower edge bound for an inclusion maximal planar drawing
-- statement:
--   An inclusion maximal finite simple graph with a crossing-free drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_82506e18_7d6a_422e_80a5_205ab3f947ca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  sorry
