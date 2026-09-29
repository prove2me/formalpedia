-- Prove2me | solution 1 for lean_workbook_plus_70711
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:43:20.734868+00:00
-- url     : https://prove2.me/submissions/83401ede-1725-44fe-afef-cbc04c830b73

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) (hn : n ≠ 0) : (1 : ℝ) / ((4 * n - 3) * (4 * n - 1)) = 1 / 2 * (1 / (4 * n - 3) - 1 / (4 * n - 1)) := by
  have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
  have hA : (4 * (n : ℝ) - 3) ≠ 0 := by linarith
  have hB : (4 * (n : ℝ) - 1) ≠ 0 := by linarith
  field_simp [hA, hB]
  <;> ring
