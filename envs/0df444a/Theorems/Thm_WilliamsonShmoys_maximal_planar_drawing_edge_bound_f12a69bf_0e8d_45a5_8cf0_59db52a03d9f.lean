-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:43:38.783881+00:00
-- url     : https://prove2.me/theorems/3daebd93-f80e-48b7-a793-c55359bffefa
-- title:
--   Edge bound for a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that cannot be extended by adding edges has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
