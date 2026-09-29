-- Prove2me | Theorems.Thm_lean_workbook_plus_65530
-- name    : lean_workbook_plus_65530
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/202a3d2a-4792-4c6f-a8ef-b44c0633c572
-- statement:
--   $\implies{ (ax + by +cz )^{2} \leq{ (a^{2} +b^{2}+c^{2})(x^{2} +y^{2}+z^{2}) }}$ , equality when $\frac{a}{x}=\frac{b}{y}=\frac{c}{z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65530 {a b c x y z : ℝ} :
  (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2)   :=  by sorry
