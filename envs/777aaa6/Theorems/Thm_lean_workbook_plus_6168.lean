-- Prove2me | Theorems.Thm_lean_workbook_plus_6168
-- name    : lean_workbook_plus_6168
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3e9ed7eb-0e09-42ff-978d-ca02f6aef35b
-- statement:
--   Prove that $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{d}>\frac{1}{a+b+c+d}$ for all positive $a, b, c$ and $d$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6168 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 / a + 1 / b + 1 / c + 1 / d > 1 / (a + b + c + d)   :=  by sorry
