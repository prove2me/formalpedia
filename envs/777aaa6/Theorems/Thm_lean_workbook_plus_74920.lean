-- Prove2me | Theorems.Thm_lean_workbook_plus_74920
-- name    : lean_workbook_plus_74920
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/aec7c362-157b-4de5-8427-16a0c123ca90
-- statement:
--   Prove that for x > 1, \\(x^{2}e^{-x^{9}}<x^{2}e^{-x^{3}}\\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74920 (x : ℝ) (hx : 1 < x) : x^2 * (Real.exp (-x^9)) < x^2 * (Real.exp (-x^3))   :=  by sorry
