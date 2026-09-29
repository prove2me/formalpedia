-- Prove2me | Theorems.Thm_lean_workbook_plus_11223
-- name    : lean_workbook_plus_11223
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e0ae477e-5c77-419d-a254-17121637fe2d
-- statement:
--   Find the limit: $\lim \left[ {n{{\left( {1 + \frac{1}{n}} \right)}^n}} \right]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11223 : ∀ (n : ℕ), ((n:ℝ) * (1 + 1/n)^n) = n * (1 + 1/n)^n   :=  by sorry
