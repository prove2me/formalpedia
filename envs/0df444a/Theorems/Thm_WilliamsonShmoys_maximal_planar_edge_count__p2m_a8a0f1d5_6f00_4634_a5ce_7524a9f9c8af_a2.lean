-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:21:11.913579+00:00
-- url     : https://prove2.me/theorems/b4f3c7d0-f80f-4201-8b80-29190a270a03
-- title:
--   Maximal planar graphs have the triangular edge count
-- statement:
--   Prove the maximal planar edge count from the given drawing and edge maximality. A route is Euler’s formula together with triangular faces, or the planar simple-graph edge bound and a planar triangulation extension; check that the argument also covers the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
