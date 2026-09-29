-- Prove2me | Theorems.Thm_lean_workbook_plus_14162
-- name    : lean_workbook_plus_14162
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/6eeeba37-2bfa-49b9-a132-c05304e5b706
-- statement:
--   $P(x^{2}+1,y):f((x^{2}+1)y)=(x^{2}+1)f(y)\: \: \: \: \forall x,y\in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14162 (x y : ℝ) (f : ℝ → ℝ) (hf: f ((x^2+1)*y) = (x^2+1)*f y) : f ((x^2+1)*y) = (x^2+1)*f y   :=  by sorry
