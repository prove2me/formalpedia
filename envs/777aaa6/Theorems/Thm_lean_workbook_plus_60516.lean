-- Prove2me | Theorems.Thm_lean_workbook_plus_60516
-- name    : lean_workbook_plus_60516
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d74f8097-fdb6-4f52-b78d-0a98b5783fce
-- statement:
--   Positive real numbers $a,b,c$ stisfy $a^2+b^2+c^2=1$ ,prove \n $\bmod{\color{red}{a+b+c+\dfrac{1}{a}+\dfrac{1}{b}+\dfrac{1}{c}\ge4\sqrt{3}}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60516 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a + b + c + 1 / a + 1 / b + 1 / c ≥ 4 * Real.sqrt 3   :=  by sorry
