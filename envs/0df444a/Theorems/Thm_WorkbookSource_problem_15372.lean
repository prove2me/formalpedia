-- Prove2me | Theorems.Thm_WorkbookSource_problem_15372
-- name    : WorkbookSource.problem_15372
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:03:40.985153+00:00
-- url     : https://prove2.me/theorems/938e1ab9-1e98-4c19-97de-382082586980
-- title:
--   Evaluating an affine function at zero
-- statement:
--   Observe that $f(x) = 2x + \frac{1}{3}$ . Then $f(0) = \frac{1}{3}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15372` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15372; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_15372  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀x, f x = 2 * x + 1 / 3) :
  f 0 = 1 / 3  :=  by sorry
