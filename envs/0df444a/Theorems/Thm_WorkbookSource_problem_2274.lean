-- Prove2me | Theorems.Thm_WorkbookSource_problem_2274
-- name    : WorkbookSource.problem_2274
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:26.648283+00:00
-- url     : https://prove2.me/theorems/6387459b-a576-4e59-96c2-303c189a2f3c
-- title:
--   A floor and fractional-part equation has no positive solution
-- statement:
--   Prove that there's no real positive solutions for $x + 2022 = \lfloor x \rfloor \cdot \{ x \}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2274` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2274; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_2274 (x : ℝ) (hx : 0 < x): ¬ (x + 2022 = Int.floor x * (x - Int.floor x))  :=  by sorry
