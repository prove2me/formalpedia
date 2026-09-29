-- Prove2me | Theorems.Thm_lean_workbook_plus_39055
-- name    : lean_workbook_plus_39055
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/fc95a7d9-411b-4997-b174-4c8af1023171
-- statement:
--   Let e be the value of the estate, 4x be the amount that the daughter got, and 3x be the amount that the son got. Then we have the equation 4x + 3x = 1/2 e, so x = 1/14 e. Then the daughter got 4/14 e and the son got 3/14 e. The mother got twice the amount that the son got, which is 6/14 e. That leaves 1/14 e for the butcher. Since he got $ 500, we have the equation 1/14 e = 500, e =
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39055 (e : ℝ) (x : ℝ) (h₁ : 4 * x + 3 * x = 1 / 2 * e) (h₂ : e = 500) : x = 1 / 14 * 500   :=  by sorry
