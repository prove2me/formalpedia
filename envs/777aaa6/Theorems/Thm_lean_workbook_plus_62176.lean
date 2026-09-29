-- Prove2me | Theorems.Thm_lean_workbook_plus_62176
-- name    : lean_workbook_plus_62176
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/caeac87c-3d2f-4357-9cc7-291da940ba38
-- statement:
--   prove that: $x^2+y^2+z^2+x+y+z\geq x^2+y^2+z^2+3\geq2(xy+xz+yz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62176 : ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 + x + y + z >= x ^ 2 + y ^ 2 + z ^ 2 + 3 ∧ x ^ 2 + y ^ 2 + z ^ 2 + 3 >= 2 * (x * y + x * z + y * z)   :=  by sorry
