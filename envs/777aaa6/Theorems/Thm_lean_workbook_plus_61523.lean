-- Prove2me | Theorems.Thm_lean_workbook_plus_61523
-- name    : lean_workbook_plus_61523
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/febc1b2e-c53f-4899-a8c4-be425fc5c8b0
-- statement:
--   Hence \n\n $$(x^2y+y^2z+z^2x)(xy^2+yz^2+zx^2)(xy+yz+zx)\ge \frac{(xy+yz+zx)^4}{3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61523 : ∀ x y z : ℝ, (x^2*y + y^2*z + z^2*x) * (x*y^2 + y*z^2 + z*x^2) * (x*y + y*z + z*x) ≥ (x*y + y*z + z*x)^4 / 3   :=  by sorry
