-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:37.420085+00:00
-- url     : https://prove2.me/theorems/d457f4af-7480-4677-bf45-35507b930e7b
-- title:
--   Matching edge lower bound for a maximal planar drawing
-- statement:
--   A finite graph with the supplied drawing that is maximal among drawable supergraphs on the same vertex set has at least `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_06103664_1c63_47e0_9ef5_c7865ee277ce_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet = H.edgeSet) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
