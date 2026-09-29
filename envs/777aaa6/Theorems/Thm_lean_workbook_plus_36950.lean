-- Prove2me | Theorems.Thm_lean_workbook_plus_36950
-- name    : lean_workbook_plus_36950
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e6958641-0f23-4d0b-a945-3fd72c5eddac
-- statement:
--   prove that: $x^2+y^2+z^2+x+y+z\geq x^2+y^2+z^2+3\geq2(xy+xz+yz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36950 : ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 + x + y + z ≥ x ^ 2 + y ^ 2 + z ^ 2 + 3 ∧ x ^ 2 + y ^ 2 + z ^ 2 + 3 ≥ 2 * (x * y + x * z + y * z)   :=  by sorry
