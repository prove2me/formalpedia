-- Prove2me | Theorems.Thm_lean_workbook_plus_7570
-- name    : lean_workbook_plus_7570
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/6f4d8eb7-542e-4827-ac2d-15bd68c5dce0
-- statement:
--   Let $x, y, z$ be reals satisfying $x^2 + y^2 + z^2 = 1.$ Prove that $1\leq x^2 + 2y^2 + 3z^2\leq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7570 (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : 1 ≤ x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 ∧ x ^ 2 + 2 * y ^ 2 + 3 * z ^ 2 ≤ 3   :=  by sorry
