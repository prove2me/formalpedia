-- Prove2me | Theorems.Thm_lean_workbook_plus_8298
-- name    : lean_workbook_plus_8298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/9b1ebe41-96ad-4533-bd9d-80e70a52b2b9
-- statement:
--   prove that : \n\n $ (x-1)^2(x^2+1)\left(3\left[x+\frac{5}{6}\right]^2+\frac{11}{12}\right) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8298 : ∀ x : ℝ, (x - 1) ^ 2 * (x ^ 2 + 1) * (3 * (x + 5 / 6) ^ 2 + 11 / 12) ≥ 0   :=  by sorry
