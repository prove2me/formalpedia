-- Prove2me | Theorems.Thm_lean_workbook_plus_17534
-- name    : lean_workbook_plus_17534
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d39fbc9e-e979-4002-a6d9-6a921f249864
-- statement:
--   If $2b - \frac{1}{c} > 1$ , then $2b > 1 + \frac{1}{c}$ $b > \frac{1}{2} + \frac{1}{2c}$ $b +1 > \frac{3}{2} + \frac{1}{2c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17534  (b c : ℝ)
  (h₀ : 2 * b - 1 / c > 1) :
  2 * b > 1 + 1 / c ∧ b > 1 / 2 + 1 / (2 * c) ∧ b + 1 > 3 / 2 + 1 / (2 * c)   :=  by sorry
