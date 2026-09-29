-- Prove2me | Theorems.Thm_WorkbookSource_problem_37856
-- name    : WorkbookSource.problem_37856
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:39:45.016649+00:00
-- url     : https://prove2.me/theorems/c01f6bd2-433f-431f-807a-db81a0f1c7df
-- title:
--   Solving a three-factor product
-- statement:
--   Let real numbers $x,y,z$ satisfy $xyz=33$, $y=1$, and $z=3$. Then
--
--   $$x=11.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37856` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37856; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_37856 (x y z : ℝ) (h₁ : x * y * z = 33) (h₂ : y = 1) (h₃ : z = 3) : x = 11  :=  by sorry
