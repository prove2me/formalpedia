-- Prove2me | Theorems.Thm_lean_workbook_plus_23323
-- name    : lean_workbook_plus_23323
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0bb41111-6677-4688-9c79-a15236547df2
-- statement:
--   For $n=999$ , prove that $\frac{1}{64}< \prod_{i=1}^{999}{\frac{2i-1}{2i}}<\frac{1}{54}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23323 : (1 / 64 : ℝ) < ∏ i in Finset.range 999, (2 * i - 1) / (2 * i) ∧ ∏ i in Finset.range 999, (2 * i - 1) / (2 * i) < 1 / 54   :=  by sorry
