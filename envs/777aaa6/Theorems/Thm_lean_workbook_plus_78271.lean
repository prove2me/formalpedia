-- Prove2me | Theorems.Thm_lean_workbook_plus_78271
-- name    : lean_workbook_plus_78271
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/46030d87-40ed-4317-bc14-a4b4e38c0068
-- statement:
--   Let $ y+z=2$ , $ x \geq 1$ , $ y \leq 0$ , $ z \geq 2$ and $ t \geq 2$ , prove that\n\n$ \frac{x^{2(t-1)}}{x^{t-1}+x^2y} \geq \frac {z}{x^2+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78271 : ∀ x y z t : ℝ, y + z = 2 ∧ x ≥ 1 ∧ y ≤ 0 ∧ z ≥ 2 ∧ t ≥ 2 → x ^ (2 * (t - 1)) / (x ^ (t - 1) + x ^ 2 * y) ≥ z / (x ^ 2 + 1)   :=  by sorry
