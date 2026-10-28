-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_count_edge_bound_1f6216d4
-- name    : WilliamsonShmoys.face_count_edge_bound_1f6216d4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:14:21.580967+00:00
-- url     : https://prove2.me/theorems/99eed061-d524-4a5f-8de4-54f4edb607ca
-- title:
--   Edge bound from finite face data
-- statement:
--   Finite face data satisfying Euler’s equation, total degree 2m, and a lower bound of three on every face degree imply the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_count_edge_bound_1f6216d4
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (F : Nat)
    (degree : Fin F → Nat)
    (heuler : Fintype.card V + F = H.edgeSet.ncard + 2)
    (hsum : (∑ f : Fin F, degree f) = 2 * H.edgeSet.ncard)
    (hdegree : ∀ f, 3 <= degree f) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
