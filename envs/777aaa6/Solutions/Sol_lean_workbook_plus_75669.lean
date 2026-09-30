-- Prove2me | solution 1 for lean_workbook_plus_75669
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:30:43.653679+00:00
-- url     : https://prove2.me/submissions/a274153b-a7d0-4b13-8e8a-3c7303f6c8c7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (n : ℕ) (hn : 0 < n) :
    Real.sqrt (n + 1) - Real.sqrt n < 1 / (2 * Real.sqrt n) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hp
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have ht := Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)
  have hinc : Real.sqrt (n : ℝ) < Real.sqrt (n + 1) :=
    Real.sqrt_lt_sqrt hp.le (by linarith)
  apply (lt_div_iff₀ (show 0 < 2 * Real.sqrt (n : ℝ) by positivity)).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr hinc)]

#print axioms solution
