-- Prove2me | Theorems.Thm_WorkbookSource_problem_16924
-- name    : WorkbookSource.problem_16924
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:21.748768+00:00
-- url     : https://prove2.me/theorems/99aba662-e3cc-4048-ba6b-cc26fe79af56
-- title:
--   Evaluating a quadratic at five halves
-- statement:
--   FF1 $ f(x) = 4x+x^2+ 2x$ Find $f$ $(\frac{5}{2})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16924` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16924; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16924 (f : ℝ → ℝ) (f_def : ∀ x, f x = 4 * x + x ^ 2 + 2 * x) : f (5 / 2) = 85 / 4  :=  by sorry
