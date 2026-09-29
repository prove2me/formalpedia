-- Prove2me | Theorems.Thm_lean_workbook_plus_26754
-- name    : lean_workbook_plus_26754
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/84f058d5-0aab-4607-ae53-a719ffc4f63e
-- statement:
--   By AM-GM, we have $\displaystyle \frac{x^2+y^2}{2}\geq xy$ , $\displaystyle \frac{x^2+z^2}{2}\geq xz$ , $\displaystyle \frac{y^2+z^2}{2}\geq yz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26754 (x y z: ℝ) : (x^2 + y^2) / 2 ≥ x * y ∧ (x^2 + z^2) / 2 ≥ x * z ∧ (y^2 + z^2) / 2 ≥ y * z   :=  by sorry
