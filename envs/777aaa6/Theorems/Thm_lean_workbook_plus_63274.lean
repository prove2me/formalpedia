-- Prove2me | Theorems.Thm_lean_workbook_plus_63274
-- name    : lean_workbook_plus_63274
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/46582ece-1155-48ce-b49a-549c3e501640
-- statement:
--   Let $a,b,c>0$ such that $a^2+b^2+c^2=1$ .Prove $\frac{a^{3}}{b^2+c}+\frac{b^{3}}{c^2+a}+\frac{c^{3}}{a^2+b}\geq \frac{\sqrt{3}}{\sqrt{3}+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63274 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^3 / (b^2 + c) + b^3 / (c^2 + a) + c^3 / (a^2 + b) ≥ Real.sqrt 3 / (Real.sqrt 3 + 1)   :=  by sorry
