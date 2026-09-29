-- Prove2me | Theorems.Thm_WorkbookSource_problem_40082
-- name    : WorkbookSource.problem_40082
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:04.441933+00:00
-- url     : https://prove2.me/theorems/ce3fd387-9d22-4931-9b2e-1dcef0befd45
-- title:
--   Reordering reciprocal terms in a cyclic expression
-- statement:
--   For real numbers $a,b,c$,
--
--   $$\left(\frac{a^2}{b^3}-\frac1a\right)+\left(\frac{b^2}{c^3}-\frac1b\right)+\left(\frac{c^2}{a^3}-\frac1c\right)=\left(\frac{a^2}{b^3}-\frac1b\right)+\left(\frac{b^2}{c^3}-\frac1c\right)+\left(\frac{c^2}{a^3}-\frac1a\right).$$
--
--   At zero denominators the source uses Lean’s total division convention.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40082` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40082; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40082 {a b c : ℝ} : (a^2 / b^3 - 1 / a) + (b^2 / c^3 - 1 / b) + (c^2 / a^3 - 1 / c) = (a^2 / b^3 - 1 / b) + (b^2 / c^3 - 1 / c) + (c^2 / a^3 - 1 / a)  :=  by sorry
