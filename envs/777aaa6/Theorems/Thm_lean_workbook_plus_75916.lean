-- Prove2me | Theorems.Thm_lean_workbook_plus_75916
-- name    : lean_workbook_plus_75916
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/75f7db3f-1a28-49e5-8d0e-83667121ef49
-- statement:
--   If $a>0, b>0, c>0, d>0$ such that $a^2+b^2+c^2+d^2=\frac{1}{4}$ prove the inequality \n\n $(a+b+c+d)(1+\frac{1}{abcd}) \geq 257.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75916 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a * b * c * d = 1) (h : a^2 + b^2 + c^2 + d^2 = 1 / 4) : (a + b + c + d) * (1 + 1 / (a * b * c * d)) ≥ 257   :=  by sorry
