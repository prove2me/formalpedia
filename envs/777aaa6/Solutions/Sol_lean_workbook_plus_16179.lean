-- Prove2me | solution 1 for lean_workbook_plus_16179
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:15:47.116339+00:00
-- url     : https://prove2.me/submissions/031b0620-8741-485c-a9a2-3cd657282a70

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c g u v : ℕ)
  (h₀ : Nat.gcd b c = g)
  (h₁ : Nat.gcd a g = 1)
  (h₂ : a * u + g * v = 1)
  (h₃ : 0 < g) :
  a * u ≡ 1 [ZMOD g] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨v, ?_⟩
  have h := congrArg (Nat.cast : ℕ → ℤ) h₂
  push_cast at h
  linarith
