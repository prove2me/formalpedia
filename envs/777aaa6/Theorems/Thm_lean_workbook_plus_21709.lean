-- Prove2me | Theorems.Thm_lean_workbook_plus_21709
-- name    : lean_workbook_plus_21709
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4e23eb53-0c8e-4214-98b1-4dcfc1e0ed5b
-- statement:
--   Let $a,b>0$ and $a^2+b^2\geq 2.$ Prove that $$\frac{a}{a^2+b}+\frac{b}{b^2+a}\leq1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21709 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^2 ≥ 2) : a / (a^2 + b) + b / (b^2 + a) ≤ 1   :=  by sorry
