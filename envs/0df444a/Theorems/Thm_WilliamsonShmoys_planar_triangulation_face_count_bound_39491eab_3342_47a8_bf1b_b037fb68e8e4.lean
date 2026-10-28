-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_face_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- name    : WilliamsonShmoys.planar_triangulation_face_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:05:25.07917+00:00
-- url     : https://prove2.me/theorems/3742e319-c32f-4be7-a28d-fa7a798187e6
-- title:
--   Exact edge count from triangular face data
-- statement:
--   The face-data equations imply the exact edge count: Euler’s relation and three sides per face, combined with two face-side incidences per edge, give the equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_face_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (d : WilliamsonShmoys.PlanarFaceCountData G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
