-- Prove2me | Theorems.Thm_lean_workbook_plus_26739
-- name    : lean_workbook_plus_26739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c61fb993-5e36-4fde-81ca-85695c368872
-- statement:
--   Let $a,b,c\geq 0 $ and $\frac{a}{a+2}+\frac{b}{b+2}+\frac{c}{c+1}=1 .$ Prove that $abc\leq \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26739 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a / (a + 2) + b / (b + 2) + c / (c + 1) = 1) : a * b * c ≤ 1 / 2   :=  by sorry
