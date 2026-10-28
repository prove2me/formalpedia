-- Prove2me | Theorems.Thm_WilliamsonShmoys_plane_euler_data_of_edge_formula
-- name    : WilliamsonShmoys.plane_euler_data_of_edge_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:10:38.891588+00:00
-- url     : https://prove2.me/theorems/0abbbec7-3776-48da-a3d2-a27140b9afe9
-- title:
--   Recover finite Euler face data from the triangulated edge count
-- statement:
--   Given n ≥ 3 and E + 6 = 3n, choose the face type `Fin (2n - 4)`. Its cardinality satisfies n + F = E + 2 and 3F = 2E, so it witnesses `HasPlaneEulerData`. This is finite-cardinality arithmetic, independent of the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlaneEulerData

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.plane_euler_data_of_edge_formula
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    WilliamsonShmoys.HasPlaneEulerData K := by
  sorry
