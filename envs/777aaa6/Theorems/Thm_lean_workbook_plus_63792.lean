-- Prove2me | Theorems.Thm_lean_workbook_plus_63792
-- name    : lean_workbook_plus_63792
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9ef25d31-279d-4394-aa74-1a105f0768f2
-- statement:
--   Let $a,b,c>0$ such that $\frac{a}{b+c}+\frac{b}{c+a}\leq\frac{3}{2}.$ Then $\frac{c}{a+b}\ge \frac{1}{6}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63792 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) ≤ 3 / 2 → c / (a + b) ≥ 1 / 6)   :=  by sorry
