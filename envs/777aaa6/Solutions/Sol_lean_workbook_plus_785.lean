-- Prove2me | solution 1 for lean_workbook_plus_785
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:57.297078+00:00
-- url     : https://prove2.me/submissions/cf72a3e2-bc46-4ff5-8eff-2f542e8e7289

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b p : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < p)
  (h₁ : a ≠ b)
  (h₂ : Nat.gcd a p = Nat.gcd b p), a * (a + p) = b * (b + p)) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
