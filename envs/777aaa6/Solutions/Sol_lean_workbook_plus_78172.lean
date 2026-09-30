-- Prove2me | solution 1 for lean_workbook_plus_78172
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:30:12.15064+00:00
-- url     : https://prove2.me/submissions/f9529551-6e41-4643-a20e-967a8352bb2c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (n : ℕ) (m k : ℕ) (h₁ : 0 ≤ k) (h₂ : k ≤ 2 * m)
    (h₃ : n = m ^ 2 + k) : ⌊Real.sqrt n⌋ = m := by
  have hn : (n : ℝ) = (m : ℝ) ^ 2 + k := by exact_mod_cast h₃
  have hk : (k : ℝ) ≤ 2 * m := by exact_mod_cast h₂
  have hlo : (m : ℝ) ≤ Real.sqrt n :=
    Real.le_sqrt_of_sq_le (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  have hhi : Real.sqrt n < (m : ℝ) + 1 := by
    apply (Real.sqrt_lt (Nat.cast_nonneg _) (by positivity)).mpr
    nlinarith
  apply Int.floor_eq_iff.mpr
  simpa only [Int.cast_natCast] using And.intro hlo hhi

#print axioms solution
