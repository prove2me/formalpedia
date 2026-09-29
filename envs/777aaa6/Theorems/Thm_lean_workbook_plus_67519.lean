-- Prove2me | Theorems.Thm_lean_workbook_plus_67519
-- name    : lean_workbook_plus_67519
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/dc002821-4f4f-436f-b984-4faded8d48e2
-- statement:
--   Prove for all positive real numbers $a,b,c$ , such that $a^2+b^2+c^2=1$ : \n\n $\frac{a^3}{b^2+c}+\frac{b^3}{c^2+a}+\frac{c^3}{a^2+b}\ge \frac{\sqrt{3}}{1+\sqrt{3}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67519 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c = 1) : a^3 / (b^2 + c) + b^3 / (c^2 + a) + c^3 / (a^2 + b) ≥ Real.sqrt 3 / (1 + Real.sqrt 3)   :=  by sorry
