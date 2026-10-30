-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_drawing_edge_count__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1
-- name    : WilliamsonShmoys.planar_maximal_drawing_edge_count__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:31:50.650751+00:00
-- url     : https://prove2.me/theorems/105a7e64-a154-40f8-8dae-11517fa32419
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A graph with a planar drawing that is maximal under adding edges on its fixed vertex set, and with at least three vertices, has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_maximal_drawing_edge_count__p2m_e311c4a7_aff6_4403_a1d3_f4a962b82e69_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
