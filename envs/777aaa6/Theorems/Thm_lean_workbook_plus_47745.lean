-- Prove2me | Theorems.Thm_lean_workbook_plus_47745
-- name    : lean_workbook_plus_47745
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/85c4ef7b-30e2-4751-9a83-9ee3c0495a39
-- statement:
--   Prove that: \(5(a^4 + b^4 + c^4) + a^2b^2 + b^2c^2 + c^2a^2 \geq 2(a^3(b+c) + b^3(c+a) + c^3(a+b) + abc(a+b+c))\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47745 (a b c : ℝ) : 5 * (a ^ 4 + b ^ 4 + c ^ 4) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ 2 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b) + a * b * c * (a + b + c))   :=  by sorry
