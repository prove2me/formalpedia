-- Prove2me | Theorems.Thm_lean_workbook_plus_64916
-- name    : lean_workbook_plus_64916
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c82e9c3a-150d-4069-bd00-fd22cdc0491c
-- statement:
--   If $a,b,c>0 $ prove that:\n $ \frac{a}{2a+b+c}+\frac{b}{2b+c+a}+\frac{c}{2c+a+b}\le\frac{3}{4} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64916 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a / (2 * a + b + c) + b / (2 * b + c + a) + c / (2 * c + a + b) ≤ 3 / 4   :=  by sorry
