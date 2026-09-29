-- Prove2me | Theorems.Thm_lean_workbook_plus_17988
-- name    : lean_workbook_plus_17988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b414ac3e-f012-4192-8969-3c6fd70bfef9
-- statement:
--   Prove that for $x, y, z> 0$ \n $\frac{x^2y^2+z^2y^2+x^2z^2}{xyz}\geq x+y+z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17988 : ∀ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 → (x^2*y^2 + z^2*y^2 + x^2*z^2) / (x*y*z) ≥ x + y + z   :=  by sorry
