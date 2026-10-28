-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:37:34.65944+00:00
-- url     : https://prove2.me/theorems/7a40fe9c-f6ae-482d-b063-0bcc590deda9
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A simple graph with a crossing-free drawing on at least three finite ordered vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
