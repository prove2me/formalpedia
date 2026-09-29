-- Prove2me | Theorems.Thm_lean_workbook_plus_39654
-- name    : lean_workbook_plus_39654
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/be97b8f3-dfc6-439f-98aa-2c1b91c28047
-- statement:
--   Let $ a,$ $ b,$ $ c$ be the side-lengths of a triangle. Prove that \n $ a^2\left(\frac {b}{c} - 1\right) + b^2\left(\frac {c}{a} - 1\right) + c^2\left(\frac {a}{b} - 1\right) \ge 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39654    (a b c : ℝ)
    (h₁ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₂ : c < a + b)
    (h₃ : b < a + c)
    (h₄ : a < b + c) :
    0 ≤ a^2 * (b / c - 1) + b^2 * (c / a - 1) + c^2 * (a / b - 1)   :=  by sorry
