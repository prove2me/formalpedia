-- Prove2me | Theorems.Thm_lean_workbook_plus_64131
-- name    : lean_workbook_plus_64131
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c309e054-400b-48b2-9f79-6226d065ed93
-- statement:
--   Equation is $-xf(x)=f(\frac 1x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64131 (x : ℝ) (f : ℝ → ℝ) (hf: f x = -x * f (1/x)) : f x = -x * f (1/x)   :=  by sorry
