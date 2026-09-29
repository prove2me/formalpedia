-- Prove2me | Theorems.Thm_lean_workbook_plus_60718
-- name    : lean_workbook_plus_60718
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/838fddd2-909c-41ee-b81c-7f0824824872
-- statement:
--   if $a+b+c=0$ then prove that $2(a^4+b^4+c^4)=(a^2+b^2+c^2)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60718 {a b c : ℝ} (h : a + b + c = 0) :
  2 * (a^4 + b^4 + c^4) = (a^2 + b^2 + c^2)^2   :=  by sorry
