-- Prove2me | solution 1 for lean_workbook_plus_22909
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:22:45.844823+00:00
-- url     : https://prove2.me/submissions/e0daa5c8-7d39-447d-a8ff-17ab5148eccf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Real.Sqrt
set_option autoImplicit false
theorem solution (n : ℕ) : Real.sqrt ((3 * n + 3) / (3 * n + 1)) ≤ (2 * n + 2) / (2 * n + 1) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd1 : 0 < 3 * (n : ℝ) + 1 := by positivity
  have hd2 : 0 < 2 * (n : ℝ) + 1 := by positivity
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  rw [div_pow]
  apply (div_le_div_iff₀ hd1 (sq_pos_of_pos hd2)).2
  nlinarith [sq_nonneg (n : ℝ)]
