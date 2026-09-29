-- Prove2me | Theorems.Thm_lean_workbook_plus_22447
-- name    : lean_workbook_plus_22447
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5845f6e4-2e21-4f28-b0f5-6667412e6d8d
-- statement:
--   Let $a,b $ be real numbers such that $a+b>= 2$ \nProve that : $a^4+b^4 >= a^3+b^3 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22447 (a b : ℝ) (ha : a + b >= 2) : a^4 + b^4 >= a^3 + b^3   :=  by sorry
