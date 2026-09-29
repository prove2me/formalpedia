-- Prove2me | Theorems.Thm_lean_workbook_plus_44565
-- name    : lean_workbook_plus_44565
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e2aae412-c232-4e78-9325-c8910fcc3e4b
-- statement:
--   If $a,b,c>0$ and $a^2+b^2+c^2=1$ , prove that:\n$\frac{a^3}{b^2+c}+\frac{b^3}{c^2+a}+\frac{c^3}{a^2+b} \ge \frac{\sqrt{3}}{1+a+b+c}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44565 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a^3 / (b^2 + c) + b^3 / (c^2 + a) + c^3 / (a^2 + b) ≥ Real.sqrt 3 / (1 + a + b + c)   :=  by sorry
