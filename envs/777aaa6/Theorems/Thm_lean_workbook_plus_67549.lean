-- Prove2me | Theorems.Thm_lean_workbook_plus_67549
-- name    : lean_workbook_plus_67549
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a24f3b83-003a-47fe-b386-c09991466ec8
-- statement:
--   Let $a,b,c>0,a^2+b^2+c^2+2abc=1.$ Prove that $$a+b + (b+c)^2 + (c+a)^3 <4.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67549 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) : a + b + (b + c)^2 + (c + a)^3 < 4   :=  by sorry
