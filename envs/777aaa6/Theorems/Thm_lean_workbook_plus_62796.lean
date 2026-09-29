-- Prove2me | Theorems.Thm_lean_workbook_plus_62796
-- name    : lean_workbook_plus_62796
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/95e1eb7f-dcec-4a7a-9b82-1fd0288bb36e
-- statement:
--   Use the Sum of Squares Formula to find the sum $\sum_{x=1}^{12} x^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62796 (n : ℕ) : ∑ x in Finset.range 12, x^2 = 650   :=  by sorry
