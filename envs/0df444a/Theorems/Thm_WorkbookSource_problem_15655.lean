-- Prove2me | Theorems.Thm_WorkbookSource_problem_15655
-- name    : WorkbookSource.problem_15655
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:03:32.945376+00:00
-- url     : https://prove2.me/theorems/c7dd1bc3-3b2a-49c9-a54d-0b01ddb1ed80
-- title:
--   Expanding a quotient product inequality
-- statement:
--   Derive the inequality $\frac{a^2}{b^2} + 1 \le \frac{5a}{2b}$ from $\left( \frac{a}{b} - \frac{1}{2} \right) \left( \frac{a}{b} -2 \right) \le 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15655` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15655; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_15655 (a b : ℝ) : (a / b - 1 / 2) * (a / b - 2) ≤ 0 → a^2 / b^2 + 1 ≤ 5 * a / (2 * b)  :=  by sorry
