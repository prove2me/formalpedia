-- Prove2me | Theorems.Thm_lean_workbook_plus_63571
-- name    : lean_workbook_plus_63571
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4a7f18ff-2ed2-417c-b45a-0e649f272a7f
-- statement:
--   The following inequality is also true:\n $ \frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\ge\frac{7}{2}-\frac{16abc}{(a+b+c)^3+5abc} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63571 : ∀ a b c : ℝ, (a / (b + c) + b / (c + a) + c / (a + b) ≥ 7 / 2 - 16 * a * b * c / ((a + b + c) ^ 3 + 5 * a * b * c))   :=  by sorry
