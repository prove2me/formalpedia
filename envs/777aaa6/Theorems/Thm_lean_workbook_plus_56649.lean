-- Prove2me | Theorems.Thm_lean_workbook_plus_56649
-- name    : lean_workbook_plus_56649
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/05f2e09e-2a7d-424d-b84a-eb0def3d32bf
-- statement:
--   $\\dfrac{x^2}{4} + y^2 + z^2\\ge xy - xz + 2yz.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56649 : ∀ x y z : ℝ, (x ^ 2 / 4 + y ^ 2 + z ^ 2) ≥ x * y - x * z + 2 * y * z   :=  by sorry
