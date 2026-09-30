-- Prove2me | solution 1 for lean_workbook_plus_62735
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:37.916572+00:00
-- url     : https://prove2.me/submissions/03b79ac8-e596-4678-8055-5b0db989242c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem constant_sequence (x : ℕ → ℝ) (x0 : x 0 = Real.sqrt 2)
    (x_rec : ∀ n, x (n + 1) = (x n + 2 / x n) / 2) :
    ∀ n, x n = Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hd : 2 / Real.sqrt 2 = Real.sqrt 2 := (div_eq_iff hs.ne').mpr (by nlinarith)
  intro n
  induction n with
  | zero => exact x0
  | succ n ih => rw [x_rec, ih, hd]; ring

theorem solution (x : ℕ → ℝ) (x0 : x 0 = Real.sqrt 2)
    (x_rec : ∀ n, x (n + 1) = (x n + 2 / x n) / 2) :
    ∃ n, ∀ ε > 0, |x n - Real.sqrt 2| < ε := by
  refine ⟨0, fun ε hε => ?_⟩
  rw [constant_sequence x x0 x_rec, sub_self, abs_zero]
  exact hε

#print axioms solution
