-- Prove2me | solution 1 for lean_workbook_plus_8439
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:48:01.664245+00:00
-- url     : https://prove2.me/submissions/440861df-ada5-44cc-aa04-213cca50b7ee

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (m : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∀ m, f (m + 1) = f m + m + 1)
  (h₁ : f 1 = 1) :
  f m = m * (m + 1) / 2 := by
  have hz : f 0=0 := by have h := h₀ 0; norm_num at h; omega
  have he (k : ℕ) : 2*f k=k*(k+1) := by
    induction k with
    | zero => simp [hz]
    | succ k ih => rw [h₀]; nlinarith only [ih]
  have h := he m
  omega
