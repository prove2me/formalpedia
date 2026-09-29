-- Prove2me | Theorems.Thm_WorkbookSource_problem_31517
-- name    : WorkbookSource.problem_31517
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:53.031841+00:00
-- url     : https://prove2.me/theorems/2b9b6ebc-8fab-42a0-8b6f-353cd472bfd9
-- title:
--   A quadratic bound in an open square
-- statement:
--   Prove that for $0<a,b<2$, $a^2 + ab + b^2 < 3(a + b)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31517` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31517; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_31517 (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a < 2 ∧ b < 2) : a^2 + a * b + b^2 < 3 * (a + b)  :=  by sorry
