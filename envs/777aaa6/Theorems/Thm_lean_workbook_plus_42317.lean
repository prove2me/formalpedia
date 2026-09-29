-- Prove2me | Theorems.Thm_lean_workbook_plus_42317
-- name    : lean_workbook_plus_42317
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/5c733c90-a4e9-4968-9b7b-63c32ffc8779
-- statement:
--   What is the discriminant of $x^{2}-16x+60=0$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42317 (a b c : ℝ) (habc : a = 1 ∧ b = -16 ∧ c = 60) : b^2 - 4*a*c = 16^2 - 4*1*60   :=  by sorry
