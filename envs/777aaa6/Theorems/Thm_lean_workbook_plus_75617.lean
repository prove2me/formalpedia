-- Prove2me | Theorems.Thm_lean_workbook_plus_75617
-- name    : lean_workbook_plus_75617
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/1ef516d7-6b15-4433-b610-1d599b9efedf
-- statement:
--   Prove that \n\n $\frac{a^3+b^3-c^3}{a+b-c} \leq \frac32 (a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75617 (a b c : ℝ) (ha : a + b > c) (hb : a + c > b) (hc : b + c > a) : (a^3 + b^3 - c^3) / (a + b - c) ≤ (3 / 2) * (a^2 + b^2 + c^2)   :=  by sorry
