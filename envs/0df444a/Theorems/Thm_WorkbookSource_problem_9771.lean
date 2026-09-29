-- Prove2me | Theorems.Thm_WorkbookSource_problem_9771
-- name    : WorkbookSource.problem_9771
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:21.807134+00:00
-- url     : https://prove2.me/theorems/50e7120e-65b0-4d01-9108-e3ba6a7efa92
-- title:
--   Completing the square in a cosine expression
-- statement:
--   $4(-\cos^2(x) + \cos(x) + \dfrac{1}{2}) = 4(-(\cos(x) - \dfrac{1}{2})^2 + \dfrac{3}{4})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9771` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9771; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9771 (x : ℝ) : 4 * (-(Real.cos x) ^ 2 + Real.cos x + 1 / 2) = 4 * (-((Real.cos x) - 1 / 2) ^ 2 + 3 / 4)  :=  by sorry
