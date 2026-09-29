-- Prove2me | solution 1 for lean_workbook_plus_43025
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:35.390583+00:00
-- url     : https://prove2.me/submissions/aa56685b-3513-4c6d-81c4-56b4ea527a71

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℕ → ℝ) (hx: ∀ n, 1 <= x n ∧ x n <= 2) : ∀ n, x n ^ 3 + 1 / x n < 8 + 1 := by
  intro n
  have ht := hx n
  have hp : 0<x n := by linarith [ht.1]
  by_cases he : x n=1
  · rw [he]
    norm_num <;> grind
  have hi : 1/x n<1 := (div_lt_iff₀ hp).mpr (by grind)
  have hc : x n^3 ≤ (2:ℝ)^3 := by gcongr; exact ht.2
  norm_num at hc
  grind
