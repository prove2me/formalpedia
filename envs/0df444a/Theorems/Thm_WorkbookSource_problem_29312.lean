-- Prove2me | Theorems.Thm_WorkbookSource_problem_29312
-- name    : WorkbookSource.problem_29312
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:58:24.10766+00:00
-- url     : https://prove2.me/theorems/a568b274-542b-4592-8ab2-9a2614fbf4f9
-- title:
--   Factoring a quadratic inequality
-- statement:
--   denote by : $ \frac{x}{y}+\frac{y}{x}=t $ , then :
--    $ t^{2}-2+4\geq 3t\Leftrightarrow (t-1)(t-2)\geq 0 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29312` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29312; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_29312 (x y t : ℝ) (hx: x ≠ 0 ∧ y ≠ 0) (h : t = x/y + y/x) :  t^2 - 2 + 4 ≥ 3 * t ↔ (t - 1) * (t - 2) ≥ 0  :=  by sorry
