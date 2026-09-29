-- Prove2me | Theorems.Thm_lean_workbook_plus_6682
-- name    : lean_workbook_plus_6682
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/bf11acec-3914-4165-9a9c-929f962c7a6b
-- statement:
--   or $2(x^{3}+y^{3}+z^{3})\geq x^{2}(y+z)+y^{2}(z+x)+z^{2}(x+y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6682 : ∀ x y z : ℝ, 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ x ^ 2 * (y + z) + y ^ 2 * (z + x) + z ^ 2 * (x + y)   :=  by sorry
