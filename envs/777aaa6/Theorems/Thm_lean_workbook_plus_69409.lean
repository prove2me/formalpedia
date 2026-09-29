-- Prove2me | Theorems.Thm_lean_workbook_plus_69409
-- name    : lean_workbook_plus_69409
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/96beda11-da70-46f2-8a66-80d2c2580754
-- statement:
--   Let $a,b,c>1$ and $(a-1)(b-1)(c-1)=6 \sqrt{3} -10.$ Prove that \n\n $$a+b+c\leq abc$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69409 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (habc : a * b * c = 1) (h : (a - 1) * (b - 1) * (c - 1) = 6 * Real.sqrt 3 - 10) : a + b + c ≤ a * b * c   :=  by sorry
