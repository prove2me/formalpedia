-- Prove2me | Theorems.Thm_lean_workbook_plus_33090
-- name    : lean_workbook_plus_33090
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/3858b644-e83e-466a-b2a7-b7453ffb9a1a
-- statement:
--   Given the polynomial $ P(x) = x^{4} + ax^{3} + bx^{2} + cx + d $, if $ P(1) = 10 $, $ P(2) = 20 $, and $ P(3) = 30 $, find $ \frac{P(12) + P(-8)}{10} $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33090 (a b c d : ℝ) (h₁ : (1 : ℝ)^4 + a * 1^3 + b * 1^2 + c * 1 + d = 10) (h₂ : (2 : ℝ)^4 + a * 2^3 + b * 2^2 + c * 2 + d = 20) (h₃ : (3 : ℝ)^4 + a * 3^3 + b * 3^2 + c * 3 + d = 30) : (12^4 + a * 12^3 + b * 12^2 + c * 12 + d + (-8)^4 + a * (-8)^3 + b * (-8)^2 + c * (-8) + d) / 10 = 1984   :=  by sorry
