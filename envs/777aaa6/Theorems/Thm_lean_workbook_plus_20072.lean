-- Prove2me | Theorems.Thm_lean_workbook_plus_20072
-- name    : lean_workbook_plus_20072
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9ff2602c-c514-4e71-a5b2-c7f15aead1d3
-- statement:
--   Prove that $(x^3y+y^3z+z^3x)^2\geq (x^3y+y^3z+z^3x)(xy^3+yz^3+zx^3) \geq (x^2y^2+y^2z^2+z^2x^2)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20072 : ∀ x y z : ℝ, (x^3 * y + y^3 * z + z^3 * x)^2 ≥ (x^3 * y + y^3 * z + z^3 * x) * (x * y^3 + y * z^3 + z * x^3) ∧ (x^3 * y + y^3 * z + z^3 * x) * (x * y^3 + y * z^3 + z * x^3) ≥ (x^2 * y^2 + y^2 * z^2 + z^2 * x^2)^2   :=  by sorry
