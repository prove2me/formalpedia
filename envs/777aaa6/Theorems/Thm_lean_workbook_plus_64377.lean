-- Prove2me | Theorems.Thm_lean_workbook_plus_64377
-- name    : lean_workbook_plus_64377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1c87a23d-e657-4507-821f-bf059d5bbfb0
-- statement:
--   $ x\ge 0$ and so $ f(x)=x+a$ and so $ f(x)^2=(x+a)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64377 (x a : ℝ) (hx: x ≥ 0) : (x + a)^2 = x^2 + 2 * a * x + a^2   :=  by sorry
