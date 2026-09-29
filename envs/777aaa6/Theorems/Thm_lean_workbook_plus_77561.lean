-- Prove2me | Theorems.Thm_lean_workbook_plus_77561
-- name    : lean_workbook_plus_77561
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6420dd35-9ff4-48c7-a6e2-256f9a846237
-- statement:
--   Prove this inequality \n ${{\left( \frac{x}{y+z} \right)}^{2}}+{{\left( \frac{y}{x+z} \right)}^{2}}+{{\left( \frac{z}{x+y} \right)}^{2}}+\frac{6xyz}{\left( x+y \right)\left( y+z \right)\left( z+x \right)}\ge \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77561 : ∀ x y z : ℝ, (x / (y + z))^2 + (y / (x + z))^2 + (z / (x + y))^2 + 6 * x * y * z / ((x + y) * (y + z) * (z + x)) ≥ 3 / 2   :=  by sorry
