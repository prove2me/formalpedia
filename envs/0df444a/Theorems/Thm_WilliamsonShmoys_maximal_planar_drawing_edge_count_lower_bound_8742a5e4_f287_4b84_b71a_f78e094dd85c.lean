-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:25:43.317587+00:00
-- url     : https://prove2.me/theorems/da46d226-71c2-4261-9a71-a0e47209e2d7
-- title:
--   Edge lower bound for a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that is maximal among drawable same-vertex-type supergraphs has at least 3n−6 edges. This supplies the lower bound in the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K = J) :
    3 * Fintype.card V - 6 ≤ J.edgeSet.ncard := by sorry
