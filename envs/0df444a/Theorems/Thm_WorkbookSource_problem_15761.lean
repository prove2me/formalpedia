-- Prove2me | Theorems.Thm_WorkbookSource_problem_15761
-- name    : WorkbookSource.problem_15761
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:37.709944+00:00
-- url     : https://prove2.me/theorems/b6b96702-eb5b-452a-ab97-7c2c413b1146
-- title:
--   An integer quadratic inequality with no solutions
-- statement:
--   Therefore we have to solve for $ n^{2}-30n+236 \leq 3 $ , which has no solutions since the discriminant is $ <0 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15761` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15761; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_15761 : ¬ (∃ n : ℤ, n^2 - 30*n + 236 ≤ 3)  :=  by sorry
