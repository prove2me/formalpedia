-- Prove2me | Theorems.Thm_lean_workbook_plus_60825
-- name    : lean_workbook_plus_60825
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/7a5ad3bc-dcdf-4851-b1ed-739dd98f6fa8
-- statement:
--   Let $ a, b,c>1 $ and $ \frac{1}{a}+\frac{2}{ b+1}+\frac{3}{ c+2}\geq \frac{5}{2}.$ Prove that $$ \left ( a-1 \right )\left ( b-1 \right )\left ( c-1 \right )\leq\frac{6}{125} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60825 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (habc : a * b * c = 1) (h : (1 / a) + (2 / (b + 1)) + (3 / (c + 2)) >= 5 / 2) : (a - 1) * (b - 1) * (c - 1) ≤ 6 / 125   :=  by sorry
