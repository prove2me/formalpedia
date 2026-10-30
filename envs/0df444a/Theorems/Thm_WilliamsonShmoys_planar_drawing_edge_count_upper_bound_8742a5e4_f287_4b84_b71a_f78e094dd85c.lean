-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:17:39.103708+00:00
-- url     : https://prove2.me/theorems/0e4a1859-8a1f-486b-9a23-3c2671c5c209
-- title:
--   Edge upper bound for a planar drawing
-- statement:
--   Every drawable simple graph on at least three finite ordered vertices has at most 3n−6 edges. This supplies the upper bound in the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_8742a5e4_f287_4b84_b71a_f78e094dd85c
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
