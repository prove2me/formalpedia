-- Prove2me | Theorems.Thm_lean_workbook_plus_81865
-- name    : lean_workbook_plus_81865
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b5f55c9f-57b1-4070-a661-205794851dbc
-- statement:
--   prove that: \n $ 4(x^2 + y^2 + z^2)\geq x + y + z + 2(xy + yz + zx) + 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81865 : ∀ x y z : ℝ, 4 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ x + y + z + 2 * (x * y + y * z + z * x) + 3   :=  by sorry
