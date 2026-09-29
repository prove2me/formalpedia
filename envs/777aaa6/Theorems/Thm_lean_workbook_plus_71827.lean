-- Prove2me | Theorems.Thm_lean_workbook_plus_71827
-- name    : lean_workbook_plus_71827
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/05ab8252-0f13-4e38-98fe-b705f864c96b
-- statement:
--   prove that: $\frac{a+1}{a^2+a+1} + \frac{b+1}{b^2+b+1} + \frac{c+1}{c^2+c+1} \le 2$ given $a,b,c \in \mathbb{R}^+$ and $abc=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71827 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a + 1) / (a ^ 2 + a + 1) + (b + 1) / (b ^ 2 + b + 1) + (c + 1) / (c ^ 2 + c + 1) ≤ 2   :=  by sorry
