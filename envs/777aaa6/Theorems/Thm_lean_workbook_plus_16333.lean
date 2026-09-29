-- Prove2me | Theorems.Thm_lean_workbook_plus_16333
-- name    : lean_workbook_plus_16333
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/33196955-0344-4cb6-a22c-da718df9db26
-- statement:
--   And it suffices to show that \n $8(a+b+c)^2\geq 6(a^2+b^2+c^2)+18(ab+bc+ca);$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16333 (a b c : ℝ) : 8 * (a + b + c) ^ 2 ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2) + 18 * (a * b + b * c + c * a)   :=  by sorry
