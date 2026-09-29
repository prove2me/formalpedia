-- Prove2me | Theorems.Thm_lean_workbook_plus_36047
-- name    : lean_workbook_plus_36047
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/72f291a3-2769-4a9e-bfa9-f6ab254e64bd
-- statement:
--   Prove that \( a,b,c\geq0\; \text{then} \) \n \( \frac{a+b}{c\sqrt{a^2+b^2}}+\frac{b+c}{a\sqrt{b^2+c^2}}+\frac{c+a}{b\sqrt{c^2+a^2}}\geq\frac{3\sqrt6}{\sqrt{a^2+b^2+c^2}}. \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36047 : ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → (a + b) / (c * Real.sqrt (a ^ 2 + b ^ 2)) + (b + c) / (a * Real.sqrt (b ^ 2 + c ^ 2)) + (c + a) / (b * Real.sqrt (c ^ 2 + a ^ 2)) ≥ 3 * Real.sqrt 6 / Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
