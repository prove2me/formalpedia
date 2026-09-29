-- Prove2me | Theorems.Thm_lean_workbook_plus_69140
-- name    : lean_workbook_plus_69140
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5ad2ebe1-928e-4c18-9ca5-10c9317b3e5c
-- statement:
--   Let $a,b,c\ge0$ and $\frac{ab}{c+1}+\frac{bc}{a+1}+\frac{ca}{b+1}+2(a+b+c)=6.$ Prove that $$ ab+bc+ca \leq 2$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69140 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : 0 < a + b + c) (h : (a * b) / (c + 1) + (b * c) / (a + 1) + (c * a) / (b + 1) + 2 * (a + b + c) = 6) : a * b + b * c + c * a ≤ 2   :=  by sorry
