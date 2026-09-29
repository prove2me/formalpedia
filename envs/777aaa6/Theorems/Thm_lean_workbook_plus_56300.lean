-- Prove2me | Theorems.Thm_lean_workbook_plus_56300
-- name    : lean_workbook_plus_56300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/92d469d9-975f-4af3-8e4c-94a0a742f723
-- statement:
--   Prove $1+x+x^{2}+x^{3}+\\dots=\frac{1}{1-x}$ for $\\mid x\\mid < 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56300 (x : ℝ) (hx : abs x < 1) :
  ∑' i : ℕ, x ^ i = 1 / (1 - x)   :=  by sorry
