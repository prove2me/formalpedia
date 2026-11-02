-- Prove2me | Theorems.Thm_planar_face_length_sum_bound__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
-- name    : planar_face_length_sum_bound__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:11:40.613471+00:00
-- url     : https://prove2.me/theorems/83726f64-252c-4cb5-9649-aa619211b6f6
-- title:
--   Lower bound from face boundary lengths
-- statement:
--   If the f face boundary lengths each are at least three and sum to 2m, then 3f ≤ 2m.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem planar_face_length_sum_bound__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
    (f m : Nat) (length : Fin f → Nat)
    (hsum : (∑ i : Fin f, length i) = 2 * m)
    (hlen : ∀ i : Fin f, 3 ≤ length i) :
    3 * f ≤ 2 * m := by sorry
