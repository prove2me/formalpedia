-- Prove2me | Theorems.Thm_lean_workbook_plus_30281
-- name    : lean_workbook_plus_30281
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/efaa741f-4f3d-4aee-bd96-6029727530bb
-- statement:
--   Write the system in the form\n$ \frac{b^2-2ab}{a^2-2ab}=\frac{117}{165}$ and from here we get\n$ { \frac{\frac{b}{a}-2}{\frac{a}{b}-2}}=\frac{117}{165}$ . By setting $ z=\frac{a}{b}$ you will get a quadratic equation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30281  (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0)
  (h₁ : a ≠ b)
  (h₂ : (b^2 - 2 * a * b) / (a^2 - 2 * a * b) = 117 / 165) :
  (b / a - 2) / (a / b - 2) = 117 / 165   :=  by sorry
