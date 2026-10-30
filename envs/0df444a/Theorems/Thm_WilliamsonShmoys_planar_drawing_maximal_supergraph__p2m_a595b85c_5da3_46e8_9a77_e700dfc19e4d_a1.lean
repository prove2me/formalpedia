-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:58:00.962148+00:00
-- url     : https://prove2.me/theorems/c52ebc15-be26-4087-8cea-444a38292ff2
-- title:
--   Maximal planar extension on the same vertices
-- statement:
--   Every finite graph with a crossing-free drawing has an edge-maximal planar supergraph on the same vertex type, and the original edge count is no larger than the extension's.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_a595b85c_5da3_46e8_9a77_e700dfc19e4d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
