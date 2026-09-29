-- Prove2me | Theorems.Thm_lean_workbook_plus_24961
-- name    : lean_workbook_plus_24961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8e63f9d4-8f9e-4d45-bf3a-199a9715134c
-- statement:
--   Let $a,b$ and $c$ be positive real numbers. Prove that \n $\frac{ab}{a+2b}+ \frac{bc}{b+2c}+\frac{ca}{c+2a} \leq \frac{a+b+c}{3}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24961 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a + 2 * b) + b * c / (b + 2 * c) + c * a / (c + 2 * a) : ℝ) ≤ (a + b + c) / 3   :=  by sorry
