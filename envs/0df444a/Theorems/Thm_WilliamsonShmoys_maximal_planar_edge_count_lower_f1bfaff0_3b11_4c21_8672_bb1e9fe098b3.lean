-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:37:22.726624+00:00
-- url     : https://prove2.me/theorems/b8029ebe-01b1-448e-8157-81d8c08a4b9d
-- title:
--   Maximality forces the planar lower edge bound
-- statement:
--   A graph maximal among planar simple graphs on the same vertex type, with at least three vertices, has at least three times its vertex count minus six edges. The proof route establishes connectedness and triangular faces, then counts face-sides using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) →
      ∀ u v, L.Adj u v → K.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
