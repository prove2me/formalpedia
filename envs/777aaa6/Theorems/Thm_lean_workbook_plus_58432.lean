-- Prove2me | Theorems.Thm_lean_workbook_plus_58432
-- name    : lean_workbook_plus_58432
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c3c367f3-f129-4c2e-a6a7-58f767c39225
-- statement:
--   $$\frac{a^2+b^2+c^2+ab+bc+ca+2}{a+b+c} \geq \frac{\frac{2}{3}(a+b+c)^2+2}{a+b+c} \geq \frac{\frac{4}{\sqrt{3}}(a+b+c)}{a+b+c}=\frac{4}{\sqrt{3}}$$ with equality for $a=b=c=\frac{\sqrt{3}}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58432 : ∀ a b c : ℝ, (a^2 + b^2 + c^2 + a * b + b * c + c * a + 2) / (a + b + c) ≥ (2 / 3 * (a + b + c)^2 + 2) / (a + b + c) ∧ (2 / 3 * (a + b + c)^2 + 2) / (a + b + c) ≥ (4 / Real.sqrt 3 * (a + b + c)) / (a + b + c)   :=  by sorry
