-- Prove2me | Theorems.Thm_WorkbookSource_problem_23650
-- name    : WorkbookSource.problem_23650
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:51:46.07332+00:00
-- url     : https://prove2.me/theorems/ef3bd0f3-0675-4d76-81f6-6b2dfcc273d0
-- title:
--   A quadratic bound above one
-- statement:
--   Let $x=\frac{a^2+b^2+c^2}{ab+bc+ca}\geq 1$ . Remain to prove:
--
--    $x^2+\frac{1}{9}(2-x)(11+4x) \geq \frac{2}{3}x+2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23650` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23650; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_23650 (x : ℝ) (hx : x ≥ 1) : x^2 + 1/9 * (2 - x) * (11 + 4 * x) ≥ 2/3 * x + 2  :=  by sorry
