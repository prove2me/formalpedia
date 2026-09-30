-- Prove2me | solution 1 for lean_workbook_plus_74648
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:15:57.834263+00:00
-- url     : https://prove2.me/submissions/f1c6c5ef-0bc5-4d39-9bd0-8a50590cb1a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (w : ℝ) : 2 * w ^ 2 + 9 ≥ 6 * Real.sqrt 2 * w := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hw := congrArg (fun t : ℝ => t * w ^ 2) hs
  nlinarith only [hw, sq_nonneg (Real.sqrt 2 * w - 3)]

#print axioms solution
