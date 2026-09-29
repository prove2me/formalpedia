-- Prove2me | Theorems.Thm_WorkbookSource_problem_27265
-- name    : WorkbookSource.problem_27265
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:25.337988+00:00
-- url     : https://prove2.me/theorems/cafe5f05-2e48-4839-bbe7-952fc1fc2072
-- title:
--   Solving a rational travel equation
-- statement:
--   Let $x$ be the desired answer, so that Qiang drove a total of $30+x$ miles in the entirety of his voyage and completed the trip within $\frac{15}{30}+\frac{x}{55}$ hours. Therefore, $\frac{x+30}{\frac{x}{55}+\frac{1}{2}}=50\Rightarrow x=\boxed{110}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27265` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27265; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_27265  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : (x + 30) / (x / 55 + 1 / 2) = 50) :
  x = 110  :=  by sorry
