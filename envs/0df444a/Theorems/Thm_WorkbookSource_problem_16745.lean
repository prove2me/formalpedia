-- Prove2me | Theorems.Thm_WorkbookSource_problem_16745
-- name    : WorkbookSource.problem_16745
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:14.435999+00:00
-- url     : https://prove2.me/theorems/29c4c675-9e5a-4e1b-be3d-d5bccf473c1a
-- title:
--   A two-variable quadratic and quartic inequality
-- statement:
--   I’m not sure but one similar inequality I think is true is $a^2 + b^2 \ge ab(2-ab)$ for an real a, b.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16745` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16745; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16745 (a b : ℝ) : a^2 + b^2 ≥ a * b * (2 - a * b)  :=  by sorry
