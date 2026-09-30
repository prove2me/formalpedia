-- Prove2me | solution 1 for lean_workbook_plus_25841
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:07:07.660638+00:00
-- url     : https://prove2.me/submissions/1edb7170-7445-46e2-b4ca-b373ac6e665e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (f : ℕ → ℝ)
    (h : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |f n - 1| < ε) :
    ∃ k : ℕ, ∀ n : ℕ, n ≥ k → f n ≥ 1 / 2 := by
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  refine ⟨N, fun n hn => ?_⟩
  have hlow := (abs_lt.mp (hN n hn)).1
  linarith

#print axioms solution
