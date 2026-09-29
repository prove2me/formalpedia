-- Prove2me | Theorems.Thm_lean_workbook_plus_23867
-- name    : lean_workbook_plus_23867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0957f5fc-f69f-4cf9-b4df-3b1d91d99f84
-- statement:
--   It's just shorthand for this -\n\n$LHS = 6(a^4+b^4+c^4+d^4) + 12(a^2b^2+a^2c^2+a^2d^2+b^2c^2+b^2d^2+c^2d^2)$\n\n$RHS = 8(a^3b+b^3a+a^3c+c^3a+a^3d+d^3a+b^3c+c^3b+b^3d+d^3b+c^3d+d^3c)$\n\nIs it always true that $LHS \ge RHS$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23867 (a b c d : ℝ) : 6 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + 12 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 + c ^ 2 * d ^ 2) ≥ 8 * (a ^ 3 * b + b ^ 3 * a + a ^ 3 * c + c ^ 3 * a + a ^ 3 * d + d ^ 3 * a + b ^ 3 * c + c ^ 3 * b + b ^ 3 * d + d ^ 3 * b + c ^ 3 * d + d ^ 3 * c)   :=  by sorry
