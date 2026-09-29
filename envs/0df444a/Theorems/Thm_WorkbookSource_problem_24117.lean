-- Prove2me | Theorems.Thm_WorkbookSource_problem_24117
-- name    : WorkbookSource.problem_24117
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:05.764236+00:00
-- url     : https://prove2.me/theorems/4a86eb01-270e-4837-a1d6-5700421995db
-- title:
--   Solving a strict linear inequality
-- statement:
--   Find all real numbers $x$ for which $3-x > x+1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24117` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24117; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_24117 (x : ℝ) : 3 - x > x + 1 ↔ x < 1  :=  by sorry
