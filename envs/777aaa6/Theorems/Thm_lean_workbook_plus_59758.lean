-- Prove2me | Theorems.Thm_lean_workbook_plus_59758
-- name    : lean_workbook_plus_59758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/04be5c2e-348c-403c-a6db-03c2907edadc
-- statement:
--   Given $x^2+y^2+z^2=1 \implies (x+y+z)^2-2(xy+yx+zx)=1 \implies m^2-2n=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59758 : ∀ x y z : ℝ, x^2 + y^2 + z^2 = 1 → (x + y + z)^2 - 2 * (x * y + y * z + z * x) = 1   :=  by sorry
