-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_drawing_edge_lower_bound
-- name    : WilliamsonShmoys.planar_maximal_drawing_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:17:34.276613+00:00
-- url     : https://prove2.me/theorems/de13c9de-cb2b-46cf-a571-237a12f3aa3d
-- title:
--   A maximum-edge drawable graph satisfies the planar edge lower bound
-- statement:
--   A drawable simple graph on at least three finite, linearly ordered vertices whose edge count is maximum among its drawable supergraphs has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_drawing_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
