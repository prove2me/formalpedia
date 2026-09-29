-- Prove2me | Theorems.Thm_WorkbookSource_problem_49999
-- name    : WorkbookSource.problem_49999
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:34.285574+00:00
-- url     : https://prove2.me/theorems/d8911f45-3ec6-4ded-b0a4-d09ecd4beeb3
-- title:
--   The mediant of two equal ratios
-- statement:
--   Given $\frac{a}{b}=\frac{c}{d}$, prove that $\frac{a+c}{b+d}=\frac{a}{b}$ using the steps: multiply both sides by $bd$, add $ab$ to both sides, apply the distributive property, and divide by $b(b+d)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49999` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49999; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_49999 (a b c d : ℝ) (h₁ : b ≠ 0) (h₂ : d ≠ 0) (h₃ : b + d ≠ 0) : a / b = c / d → (a + c) / (b + d) = a / b  :=  by sorry
