-- Prove2me | Theorems.Thm_lean_workbook_plus_65961
-- name    : lean_workbook_plus_65961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f4af1c44-bb81-4848-8497-43221eb66322
-- statement:
--   Prove that if $x,y>0$ then \n $ \frac x{y^2} + \frac y{x^2} \geq \frac 1x + \frac 1y. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65961 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x / y ^ 2 + y / x ^ 2) ≥ (1 / x + 1 / y)   :=  by sorry
