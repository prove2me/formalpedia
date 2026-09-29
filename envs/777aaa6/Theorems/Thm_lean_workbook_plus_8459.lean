-- Prove2me | Theorems.Thm_lean_workbook_plus_8459
-- name    : lean_workbook_plus_8459
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0d273492-1180-419f-a4ae-0daa3e7949cf
-- statement:
--   Prove that $ \frac{1}{2}.\frac{3}{4}.\frac{5}{6}.\frac{7}{8}......\frac{99}{100}<\frac{1}{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8459 : ∏ i in Finset.range 50, ((2 * i + 1) / (2 * i + 2)) < 1 / 10   :=  by sorry
