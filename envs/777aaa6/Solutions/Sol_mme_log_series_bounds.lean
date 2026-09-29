-- Prove2me | solution 1 for mme_log_series_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:34:50.404217+00:00
-- url     : https://prove2.me/submissions/22ef4481-c115-42db-87b1-f7044ab9a44d

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open scoped BigOperators

/-- A rational partial sum and explicit remainder enclose the logarithm of
any positive argument. Scaling the argument near one makes the remainder small. -/
theorem solution (x : ℝ) (hx : 0 < x) (n : ℕ) :
    let t := (x - 1) / (x + 1)
    let center := 2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1)
    let error := 2 * (|t| ^ (2 * n + 1) / (1 - t ^ 2))
    center - error ≤ Real.log x ∧ Real.log x ≤ center + error := by
  dsimp only
  have hden : 0 < x + 1 := by linarith
  have ht : |(x - 1) / (x + 1)| < 1 := by
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ hden).2
      linarith
    · apply (div_lt_iff₀ hden).2
      linarith
  have heq : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
    field_simp
    ring
  have h := Real.sum_range_sub_log_div_le ht n
  rw [heq, abs_le] at h
  constructor <;> linarith [h.1, h.2]


#print axioms solution
