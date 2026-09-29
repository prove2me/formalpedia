-- Prove2me | Theorems.Thm_lean_workbook_plus_6915
-- name    : lean_workbook_plus_6915
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6a71705b-cfa0-4c35-935f-a6cf823573bd
-- statement:
--   Let $ a$ , $ b$ , $ c$ be positive real numbers . Prove that $ {{a+b}\over{a+2b}} + {{b+c}\over{b+2c}} + {{c+a}\over{c+2a}}<\frac{5}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6915 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b) / (a + 2 * b) + (b + c) / (b + 2 * c) + (c + a) / (c + 2 * a) < 5 / 2   :=  by sorry
