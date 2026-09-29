-- Prove2me | Theorems.Thm_lean_workbook_plus_1162
-- name    : lean_workbook_plus_1162
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f5670ce8-afc6-460e-8a48-9426afc8f15c
-- statement:
--   $\Rightarrow 28\left( {x^4 + y^4 + z^4 } \right) \geqslant \left( {x + y + z} \right)^4 + \left( {y + z - x}\right)^4 + \left( {z + x - y} \right)^4 + \left( {x + y - z} \right)^4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1162 : ∀ x y z : ℝ, 28 * (x ^ 4 + y ^ 4 + z ^ 4) ≥ (x + y + z) ^ 4 + (y + z - x) ^ 4 + (z + x - y) ^ 4 + (x + y - z) ^ 4   :=  by sorry
