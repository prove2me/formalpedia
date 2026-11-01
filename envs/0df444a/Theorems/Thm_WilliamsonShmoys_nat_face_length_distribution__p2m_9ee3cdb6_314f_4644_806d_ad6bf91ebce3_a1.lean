-- Prove2me | Theorems.Thm_WilliamsonShmoys_nat_face_length_distribution__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- name    : WilliamsonShmoys.nat_face_length_distribution__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:42.921904+00:00
-- url     : https://prove2.me/theorems/1141cd9b-272f-416d-a43b-8cf00258b943
-- title:
--   Arithmetic construction of face-length values
-- statement:
--   Given the Euler equation, the planar edge bound, and a positive face count, one can assign `f` natural numbers, each at least three, whose sum is twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.nat_face_length_distribution__p2m_9ee3cdb6_314f_4644_806d_ad6bf91ebce3_a1
    (n E f : Nat)
    (hEuler : n + f = E + 2)
    (hBound : E + 6 ≤ 3 * n)
    (hf : 0 < f) :
    ∃ faceLength : Fin f → Nat,
      (∑ i : Fin f, faceLength i) = 2 * E ∧
      ∀ i : Fin f, 3 ≤ faceLength i := by sorry
