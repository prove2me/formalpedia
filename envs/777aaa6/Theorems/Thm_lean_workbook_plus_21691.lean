-- Prove2me | Theorems.Thm_lean_workbook_plus_21691
-- name    : lean_workbook_plus_21691
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5b5da281-fe4e-4322-a462-22a3eaaf3fb4
-- statement:
--   $x^{2}+y^{2}+z^{2}+3 \geq 2(xy+yz+zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21691 : ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 + 3 ≥ 2 * (x * y + y * z + z * x)   :=  by sorry
