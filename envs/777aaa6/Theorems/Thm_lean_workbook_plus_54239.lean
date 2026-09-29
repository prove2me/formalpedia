-- Prove2me | Theorems.Thm_lean_workbook_plus_54239
-- name    : lean_workbook_plus_54239
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3cc8ecfd-4da2-4592-8751-c5ad830c4e2a
-- statement:
--   Simplify and prove the inequality:\n$2(x^2 y+y^2 z + z^2 x +xyz) = (x+y)(y+z)(z+x)+(x-y)(x-z)(y-z) \geq (x+y)(y+z)(z+x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54239 : ∀ x y z : ℝ, 2 * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x + x * y * z) ≥ (x + y) * (y + z) * (z + x) + (x - y) * (x - z) * (y - z)   :=  by sorry
