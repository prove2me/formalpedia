-- Prove2me | Theorems.Thm_WorkbookSource_problem_3104
-- name    : WorkbookSource.problem_3104
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:32.435417+00:00
-- url     : https://prove2.me/theorems/5f013c8c-93f6-466c-83b7-de9c594da891
-- title:
--   A polynomial bound for a logarithm
-- statement:
--   Let $x=\sqrt{\frac{b}{a}}\ge 1$ and $a^2\ge 1$ then it just need to show:
--    $\frac{2x+\frac{1}{2}+\frac{x^2}{2}}{3}\ge \frac{2\ln x}{x^2-1}\Longleftrightarrow (x^2-1)(x^2+4x+1)-12\ln x\ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3104` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3104; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3104 (x : ℝ) (hx : 1 ≤ x) : (x^2 - 1) * (x^2 + 4 * x + 1) - 12 * Real.log x ≥ 0  :=  by sorry
