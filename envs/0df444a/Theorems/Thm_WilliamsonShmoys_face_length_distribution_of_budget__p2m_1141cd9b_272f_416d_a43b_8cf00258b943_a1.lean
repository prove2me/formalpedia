-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_length_distribution_of_budget__p2m_1141cd9b_272f_416d_a43b_8cf00258b943_a1
-- name    : WilliamsonShmoys.face_length_distribution_of_budget__p2m_1141cd9b_272f_416d_a43b_8cf00258b943_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:22.554258+00:00
-- url     : https://prove2.me/theorems/157c86bc-dd67-41ee-9734-dfd128d7d65c
-- title:
--   Distribute a total among face lengths
-- statement:
--   For a positive number of indices, any natural total at least three times their number can be written as the sum of values indexed by those indices, with every value at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_length_distribution_of_budget__p2m_1141cd9b_272f_416d_a43b_8cf00258b943_a1
    (f total : Nat)
    (hf : 0 < f)
    (hBudget : 3 * f ≤ total) :
    ∃ faceLength : Fin f → Nat,
      (∑ i : Fin f, faceLength i) = total ∧
      ∀ i : Fin f, 3 ≤ faceLength i := by sorry
