-- Prove2me | Theorems.Thm_mme_dwz_finite_candidate_family_common_prime_with_card_cap
-- name    : mme_dwz_finite_candidate_family_common_prime_with_card_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:03:12.131973+00:00
-- url     : https://prove2.me/theorems/01b9a8a6-ea3c-4058-b81f-51786388a54c
-- title:
--   Common prime with an ambient-cardinality cap on second-hash collisions
-- statement:
--   For a finite family of second-hash candidate sets, choose Q as the maximum candidate-set size and then choose one Bertrand prime p above the first- and second-hash budgets. Besides the standard pointwise bound and quantitative real bound Q≤R, this theorem records the essential finite fact Q≤|Outer|. The prime satisfies the displayed lower budgets and p≤2 max{4,8 max{d,Q}}, as well as the real-rate bound used in Equation (21).
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8 and the common-modulus choice in Section 6.2, printed pp. 55-57; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus

set_option autoImplicit false

theorem mme_dwz_finite_candidate_family_common_prime_with_card_cap
    {Outer Block : Type}
    [Fintype Outer] [DecidableEq Outer] [Nonempty Outer]
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    (candidates : Outer → Block → Finset Outer)
    (d : ℕ) (R : ℝ)
    (hR : ∀ retained small, ((candidates retained small).card : ℝ) ≤ R) :
    ∃ Q p : ℕ,
      (∀ retained small, (candidates retained small).card ≤ Q) ∧
      Q ≤ Fintype.card Outer ∧
      (Q : ℝ) ≤ R ∧
      p.Prime ∧ Odd p ∧
      4 < p ∧
      8 * d ≤ p ∧
      (∀ retained small, 8 * (candidates retained small).card ≤ p) ∧
      max 4 (8 * max d Q) < p ∧
      p ≤ 2 * max 4 (8 * max d Q) ∧
      (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) := by
  sorry
