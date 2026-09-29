-- Prove2me | Theorems.Thm_lean_workbook_plus_64721
-- name    : lean_workbook_plus_64721
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/7a0a17b6-1c0e-4507-8c60-76970634b93d
-- statement:
--   If a, b, c are positive numbers such that ab + bc + ca = 1, show that ${\tan ^{ - 1}}\frac{1}{a} + {\tan ^{ - 1}}\frac{1}{b} + {\tan ^{ - 1}}\frac{1}{c} = \pi$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64721 (a b c : ℝ) (habc : a * b * c = 1) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a * b < 1) (hbc : b * c < 1) (hca : a * c < 1) : tan⁻¹ (1 / a) + tan⁻¹ (1 / b) + tan⁻¹ (1 / c) = π   :=  by sorry
