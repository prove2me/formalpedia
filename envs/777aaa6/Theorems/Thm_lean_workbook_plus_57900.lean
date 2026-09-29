-- Prove2me | Theorems.Thm_lean_workbook_plus_57900
-- name    : lean_workbook_plus_57900
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9536215e-9f3d-4a3b-99f6-96160639e6cb
-- statement:
--   Find the value of the infinite geometric progression with first term 1 and common ratio \(\frac{1}{2}\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57900 (a : ℝ) (h : a = 1 / 2) : ∑' i : ℕ, a ^ i = 2   :=  by sorry
