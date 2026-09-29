-- Prove2me | Theorems.Thm_WorkbookSource_problem_35023
-- name    : WorkbookSource.problem_35023
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:35.008705+00:00
-- url     : https://prove2.me/theorems/4b3e06bf-68ac-459c-95d5-4da8aa500f0d
-- title:
--   A cyclic cubic at a specified point
-- statement:
--   For real numbers $(a,b,c)=(2/3,1/3,0)$,
--
--   $$a^2b+b^2c+c^2a=\frac4{27}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35023` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35023; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_35023 (a b c : ℝ) (h : a = 2/3 ∧ b = 1/3 ∧ c = 0) : a^2 * b + b^2 * c + c^2 * a = 4/27  :=  by sorry
