-- Prove2me | Theorems.Thm_lean_workbook_plus_39286
-- name    : lean_workbook_plus_39286
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/c58a460a-57e6-48ed-a4b7-e350567ddb04
-- statement:
--   $=\frac{n+1}{n}\cdot \frac{n+2}{n+1}\cdot \cdots \cdot \frac{2n}{2n-1}=2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39286 : ∀ n : ℕ, (∏ i in Finset.Icc 1 n, (2 * i) / (2 * i - 1)) = 2   :=  by sorry
