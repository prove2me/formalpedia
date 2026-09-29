-- Prove2me | Theorems.Thm_lean_workbook_plus_56036
-- name    : lean_workbook_plus_56036
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/59506874-1ee4-4232-b930-207ef98c64e7
-- statement:
--   Determine if the following inequality is true or false: $\frac{1}{2}*\frac{3}{4}* ... * \frac{99}{100} < \frac{1}{12}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56036 : (∏ i in Finset.Icc (1 : ℕ) 99, (i + 1) / (i + 2)) < 1 / 12   :=  by sorry
