-- Prove2me | Theorems.Thm_WilliamsonShmoys_fin_degree_sequence_from_sum_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
-- name    : WilliamsonShmoys_fin_degree_sequence_from_sum_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:54:33.546216+00:00
-- url     : https://prove2.me/theorems/20e585ce-4785-44ac-a9ad-1cfa944c9664
-- title:
--   Constructing a finite degree sequence from its sum bounds
-- statement:
--   If f is positive and 2m is at least 3f, there is a list of f natural numbers, all at least 3, whose sum is 2m. The proof sets every entry to 3 and puts the excess at index 0; the hypotheses ensure the index exists and the excess is nonnegative.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_fin_degree_sequence_from_sum_bounds__p2m_30cfc9e9_677f_431a_ae7e_f01e3291d489_a2
    (f m : ℕ)
    (hf : 0 < f)
    (hSum : 3 * f ≤ 2 * m) :
    ∃ (degrees : Fin f → ℕ),
      (∀ i, 3 ≤ degrees i) ∧
      (∑ i : Fin f, degrees i) = 2 * m := by sorry
