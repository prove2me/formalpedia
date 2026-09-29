-- Prove2me | Theorems.Thm_lean_workbook_plus_39225
-- name    : lean_workbook_plus_39225
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3442c2d0-e27d-4bda-8b1d-a964ae74d148
-- statement:
--   Prove that $ \frac{a}{a}\left( \frac{p}{q}\right)^{2}= \boxed{ \frac{a \cdot p^{2}}{a \cdot q^{2}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39225 (a p q : ℝ) : a / a * (p / q) ^ 2 = a * p ^ 2 / (a * q ^ 2)   :=  by sorry
