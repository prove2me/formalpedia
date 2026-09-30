-- Prove2me | solution 1 for lean_workbook_plus_77407
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:11:37.57577+00:00
-- url     : https://prove2.me/submissions/97d0e7d0-5940-4f38-b6ad-3b98cf7d512d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) : a + b + c = 0 →
    (a ^ 2 + b ^ 2 + c ^ 2) / 2 * (a ^ 3 + b ^ 3 + c ^ 3) / 3 =
      (a ^ 5 + b ^ 5 + c ^ 5) / 5 := by
  intro h
  have hc : c = -(a + b) := by linarith
  rw [hc]
  ring
