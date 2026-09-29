-- Prove2me | Theorems.Thm_WorkbookSource_problem_946
-- name    : WorkbookSource.problem_946
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:21.951665+00:00
-- url     : https://prove2.me/theorems/6a257480-d6fd-4f7c-8f8a-c054904be151
-- title:
--   A sum of cubes from a sum and product
-- statement:
--   c+d=7, cd=9, what is $c^3+d^3$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_946` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved. The related Open record plus_27306 omits its variable declarations; this source explicitly declares real variables.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_946; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_946 (c d : ℝ) (h₁ : c + d = 7) (h₂ : c * d = 9) : c^3 + d^3 = 154  :=  by sorry
