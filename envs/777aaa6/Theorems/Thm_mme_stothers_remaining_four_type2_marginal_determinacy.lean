-- Prove2me | Theorems.Thm_mme_stothers_remaining_four_type2_marginal_determinacy
-- name    : mme_stothers_remaining_four_type2_marginal_determinacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:10:09.216528+00:00
-- url     : https://prove2.me/theorems/fe2b4eba-b9c4-44c7-879f-9e424cb9a405
-- title:
--   Type-2 marginal determinacy for the four remaining Stothers constituents
-- statement:
--   The type-2 marginal maps in Davie--Stothers Lemma 5.1 are injective on the profile parameters for phi_125, phi_134, and phi_224. For phi_233, two profiles have the same full three-mode marginals exactly when the two aggregate statistics sigma=2a+b and mu=a+c agree. Thus the first three completion fibers are trivial, while the final case has precisely the two-parameter same-marginal fiber handled by the minimization in Lemma 5.1(v).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(ii)--(v), pp. 364--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic

set_option autoImplicit false

theorem mme_stothers_remaining_four_type2_marginal_determinacy :
    (∀ a b c a' b' c' : ℕ,
      a + c = a' + c' →
      2 * b = 2 * b' →
      a = a' →
      b + c = b' + c' →
      a = a' ∧ b = b' ∧ c = c') ∧
    (∀ a b c d a' b' c' d' : ℕ,
      a + d = a' + d' →
      b + c = b' + c' →
      a = a' →
      b + d = b' + d' →
      2 * c = 2 * c' →
      a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∧
    (∀ a b c d a' b' c' d' : ℕ,
      a + b + c = a' + b' + c' →
      a = a' →
      2 * b = 2 * b' →
      2 * c + 2 * d = 2 * c' + 2 * d' →
      a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∧
    (∀ N a b c d a' b' c' d' : ℕ,
      2 * a + b + c + d = N →
      2 * a' + b' + c' + d' = N →
      ((2 * a + b = 2 * a' + b' ∧
          2 * c + 2 * d = 2 * c' + 2 * d' ∧
          a + c = a' + c' ∧
          a + b + d = a' + b' + d') ↔
        (2 * a + b = 2 * a' + b' ∧ a + c = a' + c'))) := by
  sorry
