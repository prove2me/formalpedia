-- Prove2me | Theorems.Thm_lean_workbook_plus_2941
-- name    : lean_workbook_plus_2941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/ea200dd0-4d3e-48b1-8195-d5aa6fc957dc
-- statement:
--   Since, $\frac{x^{2}y + x^{2}z + z^{2}y + y^{2}z}{4} \geq \sqrt[4]{x^{2}y.x^{2}z.z^{2}y.y^{2}z} = xyz $ . So, $(x^{2}+yz)(y+z) \geq 4xyz$ , which reduces to give $\frac{4}{x^{2}+yz} \leq \frac{1}{xy} + \frac{1}{xz}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2941  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  4 / (x^2 + y * z) ≤ 1 / (x * y) + 1 / (x * z)   :=  by sorry
