-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:26:59.711922+00:00
-- url     : https://prove2.me/theorems/71f04473-cd3f-492e-a3fb-474970863102
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A finite simple graph with the supplied planar drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
