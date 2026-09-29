-- Prove2me | Theorems.Thm_lean_workbook_plus_52897
-- name    : lean_workbook_plus_52897
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/402791ba-25ff-4c98-b896-16d213024951
-- statement:
--   Let $ a,b,c $ be positive real numbers such that $a^2+b^2+c^2=1$ . Prove that $(\frac{1}{a}-a)(\frac{1}{b}-b)(\frac{1}{c}-c)\geq \frac{8\sqrt{3}}{9}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52897 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (1 / a - a) * (1 / b - b) * (1 / c - c) ≥ (8 * Real.sqrt 3) / 9   :=  by sorry
