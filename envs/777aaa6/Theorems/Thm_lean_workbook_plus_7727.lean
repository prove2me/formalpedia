-- Prove2me | Theorems.Thm_lean_workbook_plus_7727
-- name    : lean_workbook_plus_7727
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8421f542-c51e-4d7c-abcc-12660cddb29e
-- statement:
--   $(a+b)(\frac{1}{a}+\frac{1}{b})-4=\frac{(a-b)^2}{ab}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7727 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a + b) * (1 / a + 1 / b) - 4 = (a - b) ^ 2 / (a * b)   :=  by sorry
