-- Prove2me | Theorems.Thm_WorkbookSource_problem_57161
-- name    : WorkbookSource.problem_57161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:44:31.592643+00:00
-- url     : https://prove2.me/theorems/08962647-9996-4126-8864-bda053d14dc5
-- title:
--   A divisible sum gives a divisible sum of cubes
-- statement:
--   Given $a + b + c$ is divisible by 3, prove $a^3 + b^3 + c^3$ is also divisible by 3.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57161` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_57161 (a b c : ℤ) (h : 3 ∣ a + b + c) : 3 ∣ a^3 + b^3 + c^3  :=  by sorry
