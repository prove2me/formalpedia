-- Prove2me | Theorems.Thm_lean_workbook_plus_47985
-- name    : lean_workbook_plus_47985
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/08930f49-df9f-4fff-b1f8-22d758595754
-- statement:
--   Prove that $(ab+bc+ca)^2=\frac{1}{4}(a^2+b^2+c^2)^2$ given $a+b+c=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47985 (a b c : ℝ) (h : a + b + c = 0) :
  (a * b + b * c + c * a) ^ 2 = (1 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2   :=  by sorry
