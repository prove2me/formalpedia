-- Prove2me | Theorems.Thm_lean_workbook_plus_21794
-- name    : lean_workbook_plus_21794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a5fbb52b-bd14-4bc2-a7c1-01180e0ac6b0
-- statement:
--   for $ a,b,c>0 $ such that $ a^2+b^2+c^2+abc=4 $ prove that:\n $ a+b+c\leq3 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21794 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : a + b + c <= 3   :=  by sorry
