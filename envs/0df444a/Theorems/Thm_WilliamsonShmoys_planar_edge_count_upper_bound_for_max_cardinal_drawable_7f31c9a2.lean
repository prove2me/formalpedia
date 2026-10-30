-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_max_cardinal_drawable_7f31c9a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_max_cardinal_drawable_7f31c9a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:51:16.031642+00:00
-- url     : https://prove2.me/theorems/7f19d37e-9065-4d86-af4a-0527774a3612
-- title:
--   Planar simple graph edge upper bound for a fixed drawable graph
-- statement:
--   A drawable finite simple graph with at least three vertices has at most three times its vertex count minus six edges. This supplies the upper bound used to turn failure of the target equality into a strict shortfall.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_max_cardinal_drawable_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
