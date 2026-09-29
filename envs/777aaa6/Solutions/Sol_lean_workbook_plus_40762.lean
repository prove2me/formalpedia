-- Prove2me | solution 1 for lean_workbook_plus_40762
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:52.406602+00:00
-- url     : https://prove2.me/submissions/26bdaf83-3274-4f29-85d7-acdd5beaa452

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e : ℝ)
  (f r : ℝ → ℝ)
  (h₀ : ∀ x, r x = f x)
  (h₁ : r a = a^5)
  (h₂ : r b = b^5)
  (h₃ : r c = c^5)
  (h₄ : r d = d^5)
  (h₅ : r e = e^5)
  (h₆ : a ≠ b)
  (h₇ : a ≠ c)
  (h₈ : a ≠ d)
  (h₉ : a ≠ e)
  (h₁₀ : b ≠ c)
  (h₁₁ : b ≠ d)
  (h₁₂ : b ≠ e)
  (h₁₃ : c ≠ d)
  (h₁₄ : c ≠ e)
  (h₁₅ : d ≠ e) :
  r a + r b + r c + r d + r e = a^5 + b^5 + c^5 + d^5 + e^5 := by
  (intros; simp_all)
