-- Prove2me | Theorems.Thm_lean_workbook_plus_25222
-- name    : lean_workbook_plus_25222
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1ca7bce2-733d-4b26-a53c-5594ca9769de
-- statement:
--   Find the value of $y$ such that $f(y)=2018y$ given $f$ is surjective and $f(f(x))=2018f(x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25222 (f : ℝ → ℝ) (hf : Function.Surjective f) (h : ∀ x, f (f x) = 2018 * f x) : ∃ y, f y = 2018 * y   :=  by sorry
