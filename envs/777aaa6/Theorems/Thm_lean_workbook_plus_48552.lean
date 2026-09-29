-- Prove2me | Theorems.Thm_lean_workbook_plus_48552
-- name    : lean_workbook_plus_48552
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/1642662b-9f0e-4e7a-82a9-87af13f6c650
-- statement:
--   Prove that $\frac{1}{a^{2}}+\frac{1}{b}\ge \frac{4}{a^{2}+b}$ given $a,b,c >0$ and $abc=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48552 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / a ^ 2 + 1 / b ≥ 4 / (a ^ 2 + b)   :=  by sorry
