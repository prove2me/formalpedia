-- Prove2me | Theorems.Thm_WorkbookSource_problem_34802
-- name    : WorkbookSource.problem_34802
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:35.272235+00:00
-- url     : https://prove2.me/theorems/3d1adb30-5222-4935-aa4c-08e3aae41b7a
-- title:
--   A quadratic product minus a square
-- statement:
--   $(a^2+ab+b^2)(a^2+ac+c^2)-\left(a^2+\frac{a(b+c)}{2}+bc\right)^2=...$
--    $=\frac{3}{4}a^2(b-c)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34802` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34802; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_34802 (a b c : ℝ) : (a^2 + a * b + b^2) * (a^2 + a * c + c^2) - (a^2 + a * (b + c) / 2 + b * c)^2 = 3 / 4 * a^2 * (b - c)^2  :=  by sorry
