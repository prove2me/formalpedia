-- Prove2me | Theorems.Thm_lean_workbook_plus_60451
-- name    : lean_workbook_plus_60451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/21f160be-6219-4aee-8ee7-0763b88e27e7
-- statement:
--   Prove that $f(x)-g(x)=\\dfrac{(x+1)(\\sqrt x-1)^2}{x}\\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60451 (x : ℝ) (hx : 0 < x) : (x + 1) * (Real.sqrt x - 1) ^ 2 / x ≥ 0   :=  by sorry
