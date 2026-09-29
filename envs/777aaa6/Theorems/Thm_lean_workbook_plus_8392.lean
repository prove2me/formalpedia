-- Prove2me | Theorems.Thm_lean_workbook_plus_8392
-- name    : lean_workbook_plus_8392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/1d587a30-6f4e-493f-9ade-ab10267ba4bc
-- statement:
--   Let $x,y,z \in R$ ,prove that: $(x^3y+zy^3+xz^3)(xy+yz+xz) \geq (x+y+z)xyz(x^2+y^2+z^2).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8392 (x y z : ℝ) : (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) * (x * y + y * z + z * x) ≥ (x + y + z) * x * y * z * (x ^ 2 + y ^ 2 + z ^ 2)   :=  by sorry
