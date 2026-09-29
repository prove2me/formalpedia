-- Prove2me | Theorems.Thm_WorkbookSource_problem_19781
-- name    : WorkbookSource.problem_19781
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:05:29.003895+00:00
-- url     : https://prove2.me/theorems/c800366b-2559-4bbf-af42-a956e355d52f
-- title:
--   A strict arithmetic-geometric mean comparison
-- statement:
--   From A.M. G.M. inequality, $\sqrt{(a^2)(a^2 + 1)} < \frac{a^2 + a^2 + 1}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19781` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19781; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_19781 : ∀ a : ℝ, Real.sqrt (a^2 * (a^2 + 1)) < (a^2 + a^2 + 1) / 2  :=  by sorry
