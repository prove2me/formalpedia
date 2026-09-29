-- Prove2me | solution 1 for lean_workbook_plus_40592
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:48:06.193382+00:00
-- url     : https://prove2.me/submissions/13fd3733-68f1-4cdf-86af-1897fb43ba98

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (n : ℕ) (f : ℝ → ℝ) (hf: 0 < x ∧ x < 1) (h: ∀ n : ℕ, f x >= 1 - x ^ n): f x >= 1 := by
  have ht : Filter.Tendsto (fun k : ℕ => 1-x^k) Filter.atTop (nhds (1 : ℝ)) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hf.1.le hf.2
    simpa using tendsto_const_nhds.sub hp
  exact le_of_tendsto ht (Filter.Eventually.of_forall h)
