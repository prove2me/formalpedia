-- Prove2me | Theorems.Thm_mme_dwz_finite_candidate_family_common_prime
-- name    : mme_dwz_finite_candidate_family_common_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:46:19.140461+00:00
-- url     : https://prove2.me/theorems/1abad42c-71b2-4ac4-b545-1e14e6afacc5
-- title:
--   DWZ Equation (21): one prime for every finite candidate fiber
-- statement:
--   Let O be a nonempty finite family of retained outer objects and B a nonempty finite family of small blocks. For every pair (I,z), let C(I,z) be its finite set of compatible collision candidates, and suppose |C(I,z)| ≤ R uniformly. Given the first-hash degree d, there is an attained maximum candidate count D ≤ R and one odd prime p that works simultaneously for every pair: $$8d ≤ p, \qquad 8|C(I,z)| ≤ p \quad \text{for every }(I,z).$$ Moreover p lies in the Bertrand interval above max(4,8 max(d,D)) and obeys the real rate bound $$p ≤ \max\{8,16\max(d,R)\}.$$ This gives the quantifier order required by Claim 6.8: the modulus is chosen once before averaging over all small blocks.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Equation (21) and Section 6.3, Claim 6.8; the prime-existence step uses Bertrand's postulate.

import Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus

set_option autoImplicit false

theorem mme_dwz_finite_candidate_family_common_prime
    {Outer Block : Type}
    [Fintype Outer] [DecidableEq Outer] [Nonempty Outer]
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    (candidates : Outer → Block → Finset Outer)
    (d : ℕ) (R : ℝ)
    (hR : ∀ retained small, ((candidates retained small).card : ℝ) ≤ R) :
    ∃ D p : ℕ,
      (∀ retained small, (candidates retained small).card ≤ D) ∧
      (D : ℝ) ≤ R ∧
      p.Prime ∧ Odd p ∧
      4 < p ∧
      8 * d ≤ p ∧
      (∀ retained small, 8 * (candidates retained small).card ≤ p) ∧
      max 4 (8 * max d D) < p ∧
      p ≤ 2 * max 4 (8 * max d D) ∧
      (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) := by
  sorry
