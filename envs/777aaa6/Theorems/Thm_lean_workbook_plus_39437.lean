-- Prove2me | Theorems.Thm_lean_workbook_plus_39437
-- name    : lean_workbook_plus_39437
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d25db93d-b985-43d5-a140-8a68eb1dd6e8
-- statement:
--   Prove that $ 1+ \frac{1}{2^2}+\frac{1}{3^2}+...+\frac{1}{2012^2} < \frac{5}{3} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39437 : (∑ i in Finset.Icc 1 2012, (1 / (i + 1) ^ 2)) < 5 / 3   :=  by sorry
