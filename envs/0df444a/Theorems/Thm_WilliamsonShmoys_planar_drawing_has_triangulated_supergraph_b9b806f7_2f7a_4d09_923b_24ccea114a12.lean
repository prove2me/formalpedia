-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:42:30.626897+00:00
-- url     : https://prove2.me/theorems/4ada0e49-628e-4a26-8799-ad047dad8409
-- title:
--   Planar completion with maximal edge count
-- statement:
--   Every finite simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has a planar supergraph on the same vertices whose edge count is exactly 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_b9b806f7_2f7a_4d09_923b_24ccea114a12
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
