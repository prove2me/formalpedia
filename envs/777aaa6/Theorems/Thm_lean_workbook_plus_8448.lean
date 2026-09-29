-- Prove2me | Theorems.Thm_lean_workbook_plus_8448
-- name    : lean_workbook_plus_8448
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b859fdef-bcdc-4fe7-9933-fda9a882fed4
-- statement:
--   Let $a ,b ,c>0 $ and $a^2=4bc. $ Prove that $$(a+b+c)\left( \frac{1}{a}+\frac{1}{b}+\frac{1}{c} \right) \geq 10$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8448 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 = 4 * b * c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 10   :=  by sorry
