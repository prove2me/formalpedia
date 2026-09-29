-- Prove2me | Theorems.Thm_lean_workbook_plus_43171
-- name    : lean_workbook_plus_43171
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/73f80333-581d-4fd8-ac2f-13ce914b0148
-- statement:
--   There are $1469$ numbers in $\{1,...,2004\}$ which are divisible by at least one of 2,3 and 5
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43171 : ∑ k in Finset.filter (λ x => 2∣x ∨ 3∣x ∨ 5∣x) (Finset.Icc 1 2004), 1 = 1469   :=  by sorry
