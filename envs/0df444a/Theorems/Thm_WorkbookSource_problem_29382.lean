-- Prove2me | Theorems.Thm_WorkbookSource_problem_29382
-- name    : WorkbookSource.problem_29382
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:02.875297+00:00
-- url     : https://prove2.me/theorems/f312502e-9542-48c0-ad37-3a9bd35a9034
-- title:
--   An equation with no positive real solution
-- statement:
--   Prove that there's no real positive solutions for $x + 2022 = \lfloor x \rfloor \cdot \{ x \}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29382` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29382; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_29382 (x : ℝ) (hx : 0 < x) : x + 2022 ≠ ⌊x⌋ * (x - ⌊x⌋)  :=  by sorry
