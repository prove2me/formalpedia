-- Prove2me | Theorems.Thm_lean_workbook_plus_60274
-- name    : lean_workbook_plus_60274
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d0dbf407-94eb-4f54-af0a-3beaa2f99518
-- statement:
--   $x^{3}+y^{3}\ge x^{2}y+xy^{2};x^{3}+y^{3}+z^{3}\ge xy^{2}+yz^{2}+zx^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60274 : ∀ x y : ℝ, x ^ 3 + y ^ 3 ≥ x ^ 2 * y + x * y ^ 2 ∧ ∀ x y z : ℝ, x ^ 3 + y ^ 3 + z ^ 3 ≥ x * y ^ 2 + y * z ^ 2 + z * x ^ 2   :=  by sorry
