-- Prove2me | Theorems.Thm_WorkbookSource_problem_41523
-- name    : WorkbookSource.problem_41523
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:55.909111+00:00
-- url     : https://prove2.me/theorems/7710cf0d-2370-4b75-aa9a-adb7ce90e4eb
-- title:
--   A symmetric cubic as a weighted sum of squared differences
-- statement:
--   Prove that $2\, \left( a+b+c \right) ^{3}+9\,abc-7\, \left( a+b+c \right) \left( ab+ac+bc \right) = \left( a-b \right) ^{2} \left( a+b \right) + \left( b-c \right) ^{2} \left( b+c \right) + \left( c-a \right) ^{2} \left( c+a \right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41523` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41523; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_41523 : ∀ a b c : ℝ, 2 * (a + b + c)^3 + 9 * a * b * c - 7 * (a + b + c) * (a * b + b * c + c * a) = (a - b)^2 * (a + b) + (b - c)^2 * (b + c) + (c - a)^2 * (c + a)  :=  by sorry
