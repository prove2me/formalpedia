-- Prove2me | Theorems.Thm_lean_workbook_plus_57390
-- name    : lean_workbook_plus_57390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/ae3ff08a-537a-45db-ac65-2bfa211cf0e0
-- statement:
--   For $a, b, c>0, a^2+b^2+c^2=1$ prove that $\frac{a^2}{1+bc}+\frac{b^2}{1+ca}+\frac{c^2}{1+ab}\le\frac{3}{4(ab+bc+ca)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57390 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a^2 / (1 + b * c) + b^2 / (1 + c * a) + c^2 / (1 + a * b) ≤ 3 / (4 * (a * b + b * c + c * a))   :=  by sorry
