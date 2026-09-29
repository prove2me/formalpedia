-- Prove2me | Theorems.Thm_lean_workbook_plus_59343
-- name    : lean_workbook_plus_59343
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/bedf9d21-8a05-4ae3-91a1-1fb6b28c723f
-- statement:
--   If f is a function such that $f(x)+\frac{1}{x}\left[f\left(-\frac{1}{x}\right)\right]=3$, what is the value of $f(2)$? Express your answer as a common fraction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59343 (f : ℝ → ℝ) (hf : ∀ x ≠ 0, f x + (1/x) * f (-1/x) = 3) : f 2 = 3/4   :=  by sorry
