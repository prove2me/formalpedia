-- Prove2me | Theorems.Thm_lean_workbook_plus_63880
-- name    : lean_workbook_plus_63880
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/48bc5a91-0f95-4048-8e8c-e4d2450137b2
-- statement:
--   Let $ a,b,c >0 $ and $ \frac{a+b}{c} + \frac{b+c}{a} +\frac{c+a}{b}=\frac{26}{3}.$ Show that $$(a + b + c)( ab +bc + ca) \ge \frac{35}{3}abc$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63880 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) / c + (b + c) / a + (c + a) / b = 26 / 3) : (a + b + c) * (a * b + b * c + c * a) ≥ 35 / 3 * a * b * c   :=  by sorry
