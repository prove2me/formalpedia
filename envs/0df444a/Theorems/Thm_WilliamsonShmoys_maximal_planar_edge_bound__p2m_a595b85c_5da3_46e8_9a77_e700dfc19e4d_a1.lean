-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:58:05.914374+00:00
-- url     : https://prove2.me/theorems/fa1358d7-5b01-463f-a67b-1e1bbf77dca7
-- title:
--   Edge bound for an edge-maximal planar graph
-- statement:
--   An edge-maximal finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
