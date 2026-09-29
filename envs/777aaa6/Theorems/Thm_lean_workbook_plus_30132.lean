-- Prove2me | Theorems.Thm_lean_workbook_plus_30132
-- name    : lean_workbook_plus_30132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/434d59f3-6346-47e1-af07-ffbe35bf00f9
-- statement:
--   Prove that if A+B+C+D=1, then $ a^2+b^2+c^2+d^2>= 1/4.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30132 (a b c d: ℝ) (h: a + b + c + d = 1) :
  a^2 + b^2 + c^2 + d^2 >= 1 / 4   :=  by sorry
