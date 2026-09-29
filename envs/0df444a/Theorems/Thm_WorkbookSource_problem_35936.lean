-- Prove2me | Theorems.Thm_WorkbookSource_problem_35936
-- name    : WorkbookSource.problem_35936
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:46.833624+00:00
-- url     : https://prove2.me/theorems/3223c9ce-56bd-4b29-b86e-6dc981382607
-- title:
--   Area scaling from two rational factors
-- statement:
--   For real numbers $b,h$,
--
--   $$\frac12\left(\frac{11}{10}b\right)\left(\frac9{10}h\right)=\frac{99}{200}bh.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35936` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35936; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_35936 (b h : ℝ) : (1 / 2 * (11 / 10 * b) * (9 / 10 * h) : ℝ) = 99 / 200 * (b * h)  :=  by sorry
