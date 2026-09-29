-- Prove2me | Theorems.Thm_lean_workbook_plus_64744
-- name    : lean_workbook_plus_64744
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d585db2d-5cb6-4dfc-9500-56726adff638
-- statement:
--   $ x^2 + y^2\le 4$ becomes $ r\le 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64744 (x y r : ℝ) (h₁ : x = r * cos θ) (h₂ : y = r * sin θ) (h₃ : 0 ≤ θ ∧ θ ≤ 2 * π) (h₄ : x^2 + y^2 ≤ 4) : r ≤ 2   :=  by sorry
