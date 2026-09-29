-- Prove2me | Theorems.Thm_lean_workbook_plus_15877
-- name    : lean_workbook_plus_15877
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6430731b-bb51-4c03-988e-8d7c7fb1ea1f
-- statement:
--   Let $ a,b,c $ be the sides of a triangle. Show that $ \sum_{cyc}{a^2(\frac{b}{c} - 1)} \ge 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15877 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 * (b / c - 1) + b^2 * (c / a - 1) + c^2 * (a / b - 1) ≥ 0   :=  by sorry
