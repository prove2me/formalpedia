-- Prove2me | Theorems.Thm_lean_workbook_plus_69136
-- name    : lean_workbook_plus_69136
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4dc6f6bd-5c06-40ae-8331-5ea5685ba953
-- statement:
--   $a_n =n^2(1+\frac{1}{2^2}+...+\frac{1}{(n-1)^2})\ge n^2$ for all $n \ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69136 : ∀ n ≥ 2, (n^2 * ∑ i in Finset.Ico 1 (n-1), (1/(i+1)^2)) ≥ n^2   :=  by sorry
