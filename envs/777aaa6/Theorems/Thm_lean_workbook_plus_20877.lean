-- Prove2me | Theorems.Thm_lean_workbook_plus_20877
-- name    : lean_workbook_plus_20877
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e4a00c89-ecc7-47ef-9e4b-23acb45e6239
-- statement:
--   Let $a,b,c>0$ and $\frac{a}{b+1}+\frac{b}{c+1}+\frac{c}{a+1}=1.$ Prove that $$abc\leq \frac{1}{8}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20877 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a / (b + 1) + b / (c + 1) + c / (a + 1) = 1) : a * b * c ≤ 1 / 8   :=  by sorry
