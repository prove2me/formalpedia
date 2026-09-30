-- Prove2me | solution 1 for lean_workbook_plus_36307
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:57:09.513853+00:00
-- url     : https://prove2.me/submissions/9de8e645-299c-48b6-a7d0-9d7289b314e7

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

theorem solution (n : ℕ) (hn : 0 < n) :
    (1 / Real.sqrt n) > 2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hlt : Real.sqrt (n : ℝ) < Real.sqrt (n + 1 : ℝ) :=
    Real.sqrt_lt_sqrt hnR.le (by linarith)
  have hsq := sq_pos_of_pos (sub_pos.2 hlt)
  have hnSq := Real.sq_sqrt hnR.le
  have hn1Sq := Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)
  apply (lt_div_iff₀ hpos).2
  nlinarith

#print axioms solution
