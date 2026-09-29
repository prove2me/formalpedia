-- Prove2me | Theorems.Thm_lean_workbook_plus_39161
-- name    : lean_workbook_plus_39161
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f16dd9df-0964-4bd3-8038-55a1755435eb
-- statement:
--   Let $ a,b,c$ be sides of a triangle. Show that: $ 2(ab^2 + bc^2 + ca^2) \ge a^2b + b^2c + c^2a + 3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39161 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * (a * b^2 + b * c^2 + c * a^2) ≥ a^2 * b + b^2 * c + c^2 * a + 3 * a * b * c   :=  by sorry
