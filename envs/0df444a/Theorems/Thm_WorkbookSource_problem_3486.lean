-- Prove2me | Theorems.Thm_WorkbookSource_problem_3486
-- name    : WorkbookSource.problem_3486
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:01.513795+00:00
-- url     : https://prove2.me/theorems/603a11b4-9678-4503-9b57-1b6d6c6d0659
-- title:
--   Solving an equation with five odd numbers
-- statement:
--   If $991+993+995+997+999=5000-N$ , then $N=$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3486` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3486; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3486 (N : ℕ) : 991 + 993 + 995 + 997 + 999 = 5000 - N → N = 25  :=  by sorry
