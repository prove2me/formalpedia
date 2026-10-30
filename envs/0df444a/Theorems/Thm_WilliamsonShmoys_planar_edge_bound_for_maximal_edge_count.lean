-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_maximal_edge_count
-- name    : WilliamsonShmoys.planar_edge_bound_for_maximal_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:23:18.029481+00:00
-- url     : https://prove2.me/theorems/edcfdbd8-7b73-43c1-8372-029d3885ca2c
-- title:
--   Planar edge bound for a drawable graph
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its vertex count minus six edges. This is the usual Euler planar edge bound. Its proof route is to establish the face-count relation for a planar drawing, use that every face boundary has length at least three, and combine those facts with Euler’s formula. The strict lower-bound hypothesis on the vertex count is needed for the stated bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_for_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
