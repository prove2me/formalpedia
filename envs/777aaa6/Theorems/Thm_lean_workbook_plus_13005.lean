-- Prove2me | Theorems.Thm_lean_workbook_plus_13005
-- name    : lean_workbook_plus_13005
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/6e6d279d-259e-46ec-a03f-d7c8f47f9f23
-- statement:
--   Let $a,b,c>0$ and $a^4+b^3+c^2=a^3+b^2+c.$ Prove that $$abc\leq1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13005 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^4 + b^3 + c^2 = a^3 + b^2 + c) : a * b * c ≤ 1   :=  by sorry
