-- Prove2me | Theorems.Thm_lean_workbook_plus_82453
-- name    : lean_workbook_plus_82453
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c24c85b1-0680-46b3-ab46-24b3f824ae7c
-- statement:
--   If $a,b,c\in R^{+}$ and $a+b+c=\frac{1}{a}+\frac{1}{b}+\frac{1}{c}$ then prove the following inequality for all $n\in N$ : $(1-abc)(a^n+b^n+c^n-\frac{1}{a^n}-\frac{1}{b^n}-\frac{1}{c^n})\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82453 (a b c : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (1 - a * b * c) * (a ^ n + b ^ n + c ^ n - 1 / a ^ n - 1 / b ^ n - 1 / c ^ n) ≥ 0   :=  by sorry
