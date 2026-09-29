-- Prove2me | Theorems.Thm_WorkbookSource_problem_1160
-- name    : WorkbookSource.problem_1160
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:16.781859+00:00
-- url     : https://prove2.me/theorems/b58562a8-b13e-477b-b4c7-4d5f3f6b1dc6
-- title:
--   Extrapolating a weighted linear system
-- statement:
--   Let $a$ , $b$ , $c$ , and $d$ be real numbers such that $a+4b+9c+16d=25$ $4a+9b+16c+25d=36$ $9a+16b+25c+36d=49$ Compute $16a+25b+36c+49d$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1160` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1160; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_1160 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 25) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 36) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 49) : 16 * a + 25 * b + 36 * c + 49 * d = 64  :=  by sorry
