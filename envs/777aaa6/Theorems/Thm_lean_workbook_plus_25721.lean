-- Prove2me | Theorems.Thm_lean_workbook_plus_25721
-- name    : lean_workbook_plus_25721
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4794258b-7a0f-4a10-a19a-9359d3a5084b
-- statement:
--   Following relationship is true also:\n$ a,b,c>0,a^2+b^2+c^2+abc=4\Rightarrow 26+abc\ge 9(a+b+c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25721 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : 26 + a * b * c ≥ 9 * (a + b + c)   :=  by sorry
