-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_3109df4d_98fd_4102_824c_39bdc30faaca
-- name    : WilliamsonShmoys.maximal_planar_edge_count_3109df4d_98fd_4102_824c_39bdc30faaca
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:10:34.768033+00:00
-- url     : https://prove2.me/theorems/f1bfaff0-3b11-4c21-8672-bb1e9fe098b3
-- title:
--   Edge count of a maximal simple planar graph
-- statement:
--   A maximal simple planar graph with at least three vertices has exactly three times its vertex count minus six edges. This is the substantive geometric step: maximality yields triangular faces, and Euler’s formula together with the two face-sides per edge gives the count. The lower bound includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_3109df4d_98fd_4102_824c_39bdc30faaca
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) →
      ∀ u v, L.Adj u v → K.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
