-- Prove2me | Theorems.Thm_lean_workbook_plus_59352
-- name    : lean_workbook_plus_59352
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a9927937-ab75-4325-b6fb-3947a6400692
-- statement:
--   Find $\delta$ such that $|x^2 - 4| < \epsilon$ for all $x$ satisfying $|x - 2| < \delta$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59352 (ε : ℝ) : ∃ δ : ℝ, ∀ x : ℝ, |x - 2| < δ → |x ^ 2 - 4| < ε   :=  by sorry
