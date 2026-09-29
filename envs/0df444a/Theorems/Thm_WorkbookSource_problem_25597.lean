-- Prove2me | Theorems.Thm_WorkbookSource_problem_25597
-- name    : WorkbookSource.problem_25597
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:36:57.630978+00:00
-- url     : https://prove2.me/theorems/d3ae40ce-4706-4409-820f-72740430af02
-- title:
--   Choosing three from2014
-- statement:
--   Find the value of $\binom{2014}{3}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25597` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25597; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_25597 (h : 3 ≤ 2014) : (Nat.choose 2014 3 : ℕ) = 1359502364  :=  by sorry
