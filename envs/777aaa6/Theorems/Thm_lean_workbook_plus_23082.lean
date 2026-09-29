-- Prove2me | Theorems.Thm_lean_workbook_plus_23082
-- name    : lean_workbook_plus_23082
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f1fd8f73-f94c-4474-96e4-cc36cae5579f
-- statement:
--   Prove that $\alpha = \sum_{n=0}^{\infty}\frac{1}{(n!)^2}$ is irrational.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23082 : ¬ ∃ (a : ℚ), a = ∑' n : ℕ, (1/(n!)^2)   :=  by sorry
