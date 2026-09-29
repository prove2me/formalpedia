-- Prove2me | Theorems.Thm_WorkbookSource_problem_51213
-- name    : WorkbookSource.problem_51213
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:31.810525+00:00
-- url     : https://prove2.me/theorems/f7d734c3-d2ec-4a23-b224-9bcc9a33b31f
-- title:
--   A quadratic form as a sum of squares
-- statement:
--   Let $a,b,c$ in $R^3$. Then prove that $a^2+4b^2+8c^2\geq(3ab+4bc+2ac)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51213` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51213; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_51213 (a b c : ℝ) : a ^ 2 + 4 * b ^ 2 + 8 * c ^ 2 ≥ 3 * a * b + 4 * b * c + 2 * a * c  :=  by sorry
