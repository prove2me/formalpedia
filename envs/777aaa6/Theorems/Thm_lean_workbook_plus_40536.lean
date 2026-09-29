-- Prove2me | Theorems.Thm_lean_workbook_plus_40536
-- name    : lean_workbook_plus_40536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8f0cfa1d-8700-4d9a-94ea-f4e0d5e6e453
-- statement:
--   Let $a, b \ge 0.$ Prove that \n$$ \left ( a^2+b+\frac{3}{4} \right )\left ( b^2+a+\frac{3}{4} \right )\geq \left ( 2a+\frac{1}{2} \right )\left ( 2b+\frac{1}{2} \right ). $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40536 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a^2 + b + 3 / 4) * (b^2 + a + 3 / 4) ≥ (2 * a + 1 / 2) * (2 * b + 1 / 2)   :=  by sorry
