-- Prove2me | Theorems.Thm_lean_workbook_plus_69145
-- name    : lean_workbook_plus_69145
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ce4dd078-67be-4ab8-a224-35e5f26a5448
-- statement:
--   Given three positive real numbers $a,b,c$ such that following holds $a^2=b^2+bc$ , $b^2=c^2+ac$ Prove that $\frac{1}{c}=\frac{1}{a}+\frac{1}{b}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69145 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a^2 = b^2 + b * c) (hbc : b^2 = c^2 + c * a) : 1 / c = 1 / a + 1 / b   :=  by sorry
