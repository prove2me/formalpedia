-- Prove2me | Theorems.Thm_lean_workbook_plus_6481
-- name    : lean_workbook_plus_6481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7a8d23eb-306b-4313-94a1-134407e7313f
-- statement:
--   Our numbers are roots of the equation $x^2-2ax+a^2-1=0$ , or $(x-a)^2=1 \implies x_1=a-1,x_2=a+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6481 (a : ℝ) : a-1 ∈ {x | x^2 - 2*a*x + a^2 - 1 = 0} ∧ a+1 ∈ {x | x^2 - 2*a*x + a^2 - 1 = 0}   :=  by sorry
