-- Prove2me | Theorems.Thm_lean_workbook_plus_23900
-- name    : lean_workbook_plus_23900
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/a1b16ffb-e92a-4a77-977f-90bed9fddfba
-- statement:
--   Let $a,b$ be reals such that $ (a+1)(a+b-1)=1 $ .Prove that $$(a^2+1)(b^2+1)\ge \frac{5}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23900 (a b : ℝ) (h : (a + 1) * (a + b - 1) = 1) : (a^2 + 1) * (b^2 + 1) ≥ 5 / 2   :=  by sorry
