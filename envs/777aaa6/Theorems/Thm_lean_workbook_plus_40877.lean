-- Prove2me | Theorems.Thm_lean_workbook_plus_40877
-- name    : lean_workbook_plus_40877
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6d8df8dd-0d6c-4e89-ab56-622735f85a38
-- statement:
--   for $\sum_{k=2}^{20}(\frac{1}{k}-\frac{1}{k+1}) =(\frac{1}{2}-\frac{1}{3})+(\frac{1}{3}-\frac{1}{4})+...+(\frac{1}{20}-\frac{1}{21})= \frac{1}{2}-\frac{1}{21}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40877 :
  ∑ k in (Finset.Icc 2 20), (1 / k - 1 / (k + 1)) = 1 / 2 - 1 / 21   :=  by sorry
