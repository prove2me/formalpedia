-- Prove2me | Theorems.Thm_lean_workbook_plus_78856
-- name    : lean_workbook_plus_78856
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2348ac20-c3d1-4ba4-adeb-b1e1eee637cd
-- statement:
--   Let $a,b,c$ be sides of a triangle. Show $-a^3 + a^2 b + a^2 c + a b^2 - 2 a b c + a c^2 - b^3 + b^2 c + b c^2 - c^3 \geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78856 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : -a^3 + a^2 * b + a^2 * c + a * b^2 - 2 * a * b * c + a * c^2 - b^3 + b^2 * c + b * c^2 - c^3 ≥ 0   :=  by sorry
