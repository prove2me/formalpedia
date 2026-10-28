-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_of_drawing_fc016acd_24e0_4b4c_9f94_11715a39d633
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_of_drawing_fc016acd_24e0_4b4c_9f94_11715a39d633
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:08:35.886814+00:00
-- url     : https://prove2.me/theorems/8c9b5a27-aa8a-47a8-b9d4-ce06b6989ef5
-- title:
--   Planar drawing edge bound
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_of_drawing_fc016acd_24e0_4b4c_9f94_11715a39d633
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
