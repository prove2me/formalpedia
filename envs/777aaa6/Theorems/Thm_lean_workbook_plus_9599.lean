-- Prove2me | Theorems.Thm_lean_workbook_plus_9599
-- name    : lean_workbook_plus_9599
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/cfd1d5ed-163b-47c8-98f7-681727c95d50
-- statement:
--   Put $ a=\frac{1}{x},b=\frac{1}{y},c=\frac{1}{z}$ , then this inequality becomes \n $ \frac{x^4+y^4+z^4}{x^4y^4z^4} \ge \frac{1}{xyz} ( \frac{1}{x^2y^3}+\frac{1}{y^2z^3}+\frac{1}{z^2x^3})$ \n $ \Leftrightarrow x^4+y^4+z^4 \ge x^3y+y^3z+z^3x$ \nwhich is obviously true by AM-GM.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9599  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  x^4 + y^4 + z^4 ≥ x^3 * y + y^3 * z + z^3 * x   :=  by sorry
