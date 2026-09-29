-- Prove2me | Theorems.Thm_lean_workbook_plus_21525
-- name    : lean_workbook_plus_21525
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0b31bb68-8f40-4b87-8db0-c144797fe17f
-- statement:
--   $b^2 (x^2 +y^2 ) + a^2 x^2 + 2bxy(a+c) + c^2 y^2 \le (1-a^2 - b^2 - c^2 ) (b^2 + \frac {a^2 + c^2 }{ 2} + \sqrt{b^2 (a+c)^2 + ( \frac{c^2 - a^2}{2})^2 }).$ Let $f(a,b,c) = b^2 + \frac {a^2 + c^2 }{ 2} + \sqrt{b^2 (a+c)^2 + ( \frac{c^2 - a^2}{2})^2 } $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21525   ∀ a b c : ℝ, (b^2 * (x^2 + y^2) + a^2 * x^2 + 2 * b * x * (a + c) + c^2 * y^2) ≤ (1 - a^2 - b^2 - c^2) * (b^2 + (a^2 + c^2) / 2 + Real.sqrt (b^2 * (a + c)^2 + ((c^2 - a^2) / 2)^2))   :=  by sorry
