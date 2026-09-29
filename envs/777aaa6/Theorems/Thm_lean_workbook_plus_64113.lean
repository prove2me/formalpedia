-- Prove2me | Theorems.Thm_lean_workbook_plus_64113
-- name    : lean_workbook_plus_64113
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d1673b15-858b-4e1d-848c-45b7f11fd42f
-- statement:
--   It is known that $a,b,c>0$ , $\frac{1}{a^3+1}+\frac{1}{b^3+1}+\frac{1}{c^3+1}=1$ .Prove that: $abc{\ge}2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64113 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (1 / (a^3 + 1)) + (1 / (b^3 + 1)) + (1 / (c^3 + 1)) = 1) : a * b * c ≥ 2   :=  by sorry
