-- Prove2me | Theorems.Thm_lean_workbook_plus_75434
-- name    : lean_workbook_plus_75434
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/fd526310-5364-46eb-8f87-da4573d67427
-- statement:
--   Prove that $\prod_{i=1}^{999}{\frac{2i-1}{2i}}<\frac{\sqrt{5991}}{3996}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75434 : ∏ i in Finset.range 999, ((2 * i - 1) / (2 * i)) < (Real.sqrt 5991) / 3996   :=  by sorry
