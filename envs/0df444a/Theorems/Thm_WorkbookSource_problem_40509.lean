-- Prove2me | Theorems.Thm_WorkbookSource_problem_40509
-- name    : WorkbookSource.problem_40509
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:47.304294+00:00
-- url     : https://prove2.me/theorems/e11c251d-2dd8-46fa-95a2-c069bf881152
-- title:
--   Factoring the denominator of a cubic quotient
-- statement:
--   Prove that $\displaystyle \frac{a^3}{b^3+c^3}=\frac{a}{b+c}\cdot \frac{a^2}{b^2+c^2-bc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40509` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40509; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40509 : ∀ a b c : ℝ, (a^3 / (b^3 + c^3) : ℝ) = (a / (b + c) : ℝ) * (a^2 / (b^2 + c^2 - b * c) : ℝ)  :=  by sorry
