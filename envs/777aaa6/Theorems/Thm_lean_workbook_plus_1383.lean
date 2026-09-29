-- Prove2me | Theorems.Thm_lean_workbook_plus_1383
-- name    : lean_workbook_plus_1383
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8a5a18d2-b761-4938-8bef-d7e4ed6d3529
-- statement:
--   Prove that $\dfrac{x^2}{4} + y^2 + z^2\ge xy - xz + 2yz.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1383 (x y z : ℝ) : (x ^ 2 / 4 + y ^ 2 + z ^ 2) ≥ x * y - x * z + 2 * y * z   :=  by sorry
