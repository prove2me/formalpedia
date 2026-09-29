-- Prove2me | Theorems.Thm_WorkbookSource_problem_6963
-- name    : WorkbookSource.problem_6963
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:45:52.094883+00:00
-- url     : https://prove2.me/theorems/fbd1c99e-2f82-4bd7-9d0e-9b51db738d65
-- title:
--   A reciprocal form of the three-variable quadratic mean bound
-- statement:
--   prove that \\( \frac {(a + b + c)}{S + \frac {1}{9}(a + b + c)^2}\le\frac {9}{4(a + b + c)} \\), where \\( S = a^2 + b^2 + c^2 \\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6963` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6963; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_6963 (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0) :
  (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2 + (1 / 9) * (a + b + c) ^ 2) ≤ 9 / (4 * (a + b + c))  :=  by sorry
