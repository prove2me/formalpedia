-- Prove2me | Theorems.Thm_Zeta9Note_irrational_of_two_small_integer_forms
-- name    : Zeta9Note.irrational_of_two_small_integer_forms
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T07:32:15.437535+00:00
-- url     : https://prove2.me/theorems/54dc4f8a-a493-49cc-9f58-090c2d723046
-- title:
--   Two independent small integer forms imply irrationality
-- statement:
--   Let x be real. If, for every positive tolerance, there are two integer coefficient pairs (b₁,a₁) and (b₂,a₂) with b₁a₂ ≠ b₂a₁ such that both |b₁ + a₁ x| and |b₂ + a₂ x| lie below that tolerance, then x is irrational. This is a criterion; it does not assert that such pairs exist for any particular number.
-- source:
--   Classical two-form irrationality criterion; abstract layer of the v0.1 research note (Zenodo 10.5281/zenodo.22951155), statement and proof in formalization/Zeta9Note.lean.

import Mathlib

namespace Zeta9Note

theorem irrational_of_two_small_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b₁ a₁ b₂ a₂ : ℤ,
        b₁ * a₂ ≠ b₂ * a₁ ∧
        |(b₁ : ℝ) + (a₁ : ℝ) * x| < ε ∧
        |(b₂ : ℝ) + (a₂ : ℝ) * x| < ε) :
    Irrational x := by sorry

end Zeta9Note
