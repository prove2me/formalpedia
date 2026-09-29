-- Prove2me | Theorems.Thm_lean_workbook_plus_46
-- name    : lean_workbook_plus_46
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3e9568a7-c34a-498e-817a-cf604639a3c6
-- statement:
--   Another shortcut would be to notice that $55_6 + 1_6 = 100_6$ . Thus, your fraction in decimal is $\frac{4 \cdot 6 + 1}{6^2 - 1}$ , or $\frac{25}{35} = \frac{5}{7}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46 :
  ((4 * 6 + 1) : ℚ) / (6^2 - 1) = 5/7   :=  by sorry
