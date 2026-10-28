-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_edge_bound
-- name    : WilliamsonShmoys.face_data_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:05:27.485815+00:00
-- url     : https://prove2.me/theorems/0bb0095c-79b6-4fc7-a95c-a5480e5281c3
-- title:
--   Euler and face-side counts imply the planar edge bound
-- statement:
--   A finite graph with a face count satisfying the stated Euler equation and summed face-side bound has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_data_edge_bound
    {V : Type} [Fintype V]
    (J : SimpleGraph V)
    (hData : ∃ F : ℕ, Fintype.card V + F = J.edgeSet.ncard + 2 ∧
      3 * F <= 2 * J.edgeSet.ncard) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
