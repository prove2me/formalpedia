-- Prove2me | Theorems.Thm_WorkbookSource_problem_55974
-- name    : WorkbookSource.problem_55974
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:50.77098+00:00
-- url     : https://prove2.me/theorems/eb2d9107-4310-431c-9f27-25005f19641d
-- title:
--   A square-sum bound above a unit average
-- statement:
--   Let $a,b,c>0$ such that $a+b+c\geq3$. Prove the inequality: i) $a^2 +b^2+c^2\geq a+b+c$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55974` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55974; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_55974 (a b c : ℝ) (h1 : a + b + c ≥ 3) (h2 : a > 0 ∧ b > 0 ∧ c > 0): a^2 + b^2 + c^2 ≥ a + b + c  :=  by sorry
