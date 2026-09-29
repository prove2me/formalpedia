-- Prove2me | Theorems.Thm_WorkbookSource_problem_33282
-- name    : WorkbookSource.problem_33282
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:59:09.206596+00:00
-- url     : https://prove2.me/theorems/376067ba-db15-4dc9-a6dd-d7c5ba44fd5a
-- title:
--   The sign of a rational polynomial expression
-- statement:
--   we have $(\forall a\le \frac{4}{3}):\frac{(3a-4)(3a-1)^2}{50(1+a^2)}\le0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33282` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33282; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_33282 : ∀ a ≤ (4:ℝ) / 3, (3 * a - 4) * (3 * a - 1) ^ 2 / (50 * (1 + a ^ 2)) ≤ 0  :=  by sorry
