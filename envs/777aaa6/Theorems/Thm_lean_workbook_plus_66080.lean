-- Prove2me | Theorems.Thm_lean_workbook_plus_66080
-- name    : lean_workbook_plus_66080
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1380a59b-17f1-4b3d-a065-abeb0ea36d1f
-- statement:
--   $a+b=c+d \implies a-c=d-b \implies a^2-2ac+c^2=d^2-2bd+b^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66080 {a b c d : ℝ} (habc : a + b = c + d) (hab : a - c = d - b) : a^2 - 2 * a * c + c^2 = d^2 - 2 * b * d + b^2   :=  by sorry
