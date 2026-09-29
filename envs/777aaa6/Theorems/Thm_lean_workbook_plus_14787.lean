-- Prove2me | Theorems.Thm_lean_workbook_plus_14787
-- name    : lean_workbook_plus_14787
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f650e60a-6952-4a10-8903-d650d0683150
-- statement:
--   Let $t = x-\frac{1}{x}=2$ . Then: \n $\frac{x^2}{x^4+1}=\frac{1}{x^2+\frac{1}{x^2}}=\frac{1}{(x-\frac{1}{x})^2+2}=\frac{1}{t^2+2}=\frac{1}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14787 (x : ℝ) (hx : x - 1/x = 2) : x^2/(x^4 + 1) = 1/6   :=  by sorry
