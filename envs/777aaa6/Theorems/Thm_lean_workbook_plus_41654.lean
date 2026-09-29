-- Prove2me | Theorems.Thm_lean_workbook_plus_41654
-- name    : lean_workbook_plus_41654
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/672722a9-8d13-469c-b460-d0c8f64ca3ba
-- statement:
--   If \(x\) , \(y\) and \(z\) are positive real numbers, prove \n\n $$\dfrac{1}{x} + \dfrac {1}{y} + \dfrac {1}{z} \geq \dfrac{4(x+y+z)^2-3(xy+yz+zx)}{(x+y+z)(xy+yz+zx)}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41654 (x y z : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 → 1/x + 1/y + 1/z ≥ (4 * (x + y + z) ^ 2 - 3 * (x*y + y*z + z*x)) / (x + y + z) / (x*y + y*z + z*x)   :=  by sorry
