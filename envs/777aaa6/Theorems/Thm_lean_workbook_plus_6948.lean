-- Prove2me | Theorems.Thm_lean_workbook_plus_6948
-- name    : lean_workbook_plus_6948
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/827d1003-d1dc-4382-9b79-c143dbddc558
-- statement:
--   For 4th power polynomial $P(x)$ we're given: $P(2) = P(1) = P(-1) = -2$ and $P(-2) = P(3) = 14$. Then find $P(0).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6948 (a b c d e f : ℝ) (h₁ : a*2^4 + b*2^3 + c*2^2 + d*2 + e = -2) (h₂ : a + b + c + d + e = -2) (h₃ : a*(-1)^4 + b*(-1)^3 + c*(-1)^2 + d*(-1) + e = -2) (h₄ : a*(-2)^4 + b*(-2)^3 + c*(-2)^2 + d*(-2) + e = 14) (h₅ : a*3^4 + b*3^3 + c*3^2 + d*3 + e = 14) : a*0^4 + b*0^3 + c*0^2 + d*0 + e = -2   :=  by sorry
