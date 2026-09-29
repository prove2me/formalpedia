-- Prove2me | Theorems.Thm_lean_workbook_plus_23177
-- name    : lean_workbook_plus_23177
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1c018adc-b385-4953-87e7-12a03f241836
-- statement:
--   The sum of the first $n$ odd numbers equals $n \times n$ , where $n$ is any natural number. For example, $1+3+5+7+9+11 = 6\times6 = 6^2 = 36$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23177 (n : ℕ) : ∑ k in Finset.range n, (2 * k + 1) = n * n   :=  by sorry
