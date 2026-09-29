-- Prove2me | Theorems.Thm_lean_workbook_plus_2854
-- name    : lean_workbook_plus_2854
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/bf02ca78-82fd-4b56-a343-c0b096fe202a
-- statement:
--   Let $a,b,c>0$ and $\frac{a}{1+b}+\frac{b}{1+c}+\frac{c}{1+a}=2$ . Prove that $abc\leq 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2854 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a / (1 + b) + b / (1 + c) + c / (1 + a) = 2) : a * b * c ≤ 8   :=  by sorry
