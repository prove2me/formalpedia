-- Prove2me | Theorems.Thm_lean_workbook_plus_33576
-- name    : lean_workbook_plus_33576
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/7c8ef92f-6f4f-4449-8861-bac1d5f3b8e4
-- statement:
--   Find the maximum value of $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}$ given that $(\frac{1}{x}, \frac{1}{y}, \frac{1}{z})=(a,b,c)$ and $a+b+c=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33576 (a b c x y z : ℝ) (h₁ : a + b + c = 1) (h₂ : x = 1 / a) (h₃ : y = 1 / b) (h₄ : z = 1 / c) : (1 / x + 1 / y + 1 / z) ≤ 3   :=  by sorry
