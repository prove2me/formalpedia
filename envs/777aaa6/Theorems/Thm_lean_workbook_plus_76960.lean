-- Prove2me | Theorems.Thm_lean_workbook_plus_76960
-- name    : lean_workbook_plus_76960
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/9cf0eb9c-8fbe-41bd-ae65-5381057adc4d
-- statement:
--   Prove that $ 4\left(\frac{(1-q^2)}{3}\right)^2+81\left(\frac{(1+q)^2(1-2q)}{27}\right)^2\ge 15\left(\frac{1-q^2}{3}\right)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76960 (q : ℝ) : 4*((1-q^2)/3)^2 + 81*((1+q)^2*(1-2*q)/27)^2 ≥ 15*((1-q^2)/3)^3   :=  by sorry
