-- Prove2me | Theorems.Thm_WorkbookSource_problem_16851
-- name    : WorkbookSource.problem_16851
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:12.809257+00:00
-- url     : https://prove2.me/theorems/775ee555-5c4b-49c7-ab85-db854ad3378a
-- title:
--   Solving a product equation for its second variable
-- statement:
--   Combine all the fractions to get:
--
--    $ \frac{y+x^{2}+1}{xy}=1$ .
--
--    Solving for $ y$ gives:
--
--    $ y=\frac{x^{2}+1}{x-1}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16851` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16851; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16851  (x y : ℝ)
  (h₀ : x ≠ 1)
  (h₁ : x * y ≠ 0)
  (h₂ : (x - 1) * y = x * x + 1) :
  y = (x * x + 1) / (x - 1)  :=  by sorry
