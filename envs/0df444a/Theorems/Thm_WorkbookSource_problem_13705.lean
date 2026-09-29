-- Prove2me | Theorems.Thm_WorkbookSource_problem_13705
-- name    : WorkbookSource.problem_13705
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:02:35.486988+00:00
-- url     : https://prove2.me/theorems/2da37126-5e9a-4c78-a571-6aa51645f7aa
-- title:
--   An inequality between ordered consecutive gaps
-- statement:
--   Let $a\geqslant b\geqslant c$ and $a-b=x, b-c=y$ . Then the inequality is equivalent to $(x+y+(x+y))^2 \geqslant 2(x^2+y^2+(x+y)^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13705` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13705; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13705 {a b c x y : ℝ} (h₁ : a ≥ b ∧ b ≥ c) (h₂ : x = a - b) (h₃ : y = b - c) : (x + y + (x + y))^2 ≥ 2 * (x^2 + y^2 + (x + y)^2)  :=  by sorry
