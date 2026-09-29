-- Prove2me | Theorems.Thm_WorkbookSource_problem_6918
-- name    : WorkbookSource.problem_6918
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:56.021656+00:00
-- url     : https://prove2.me/theorems/347dd053-856f-4d07-a2bb-5376fb38c693
-- title:
--   A reciprocal constraint implies a weighted lower bound
-- statement:
--   Let $a,b$ be positive reals such that $\frac{1}{1+a}+\frac{1}{1+b^{2}}=1.$ Prove that $$a+2b\geq 3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6918` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6918; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_6918 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / (1 + a) + 1 / (1 + b^2) = 1) : a + 2 * b ≥ 3  :=  by sorry
