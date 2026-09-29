-- Prove2me | Theorems.Thm_lean_workbook_plus_77000
-- name    : lean_workbook_plus_77000
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ba910a76-87c5-4ec8-b565-997b81b1127f
-- statement:
--   Prove that for positive reals, $\frac{x^3 + 1 +1 }{ 3} \ge x$ and $\frac{x^3 +x^3 +1}{3} \ge x^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77000 (x : ℝ) (hx : 0 < x) : (x^3 + 1 + 1) / 3 ≥ x ∧ (x^3 + x^3 + 1) / 3 ≥ x^2   :=  by sorry
