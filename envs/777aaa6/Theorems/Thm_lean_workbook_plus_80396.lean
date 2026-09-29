-- Prove2me | Theorems.Thm_lean_workbook_plus_80396
-- name    : lean_workbook_plus_80396
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1d5068ad-7a68-487d-b776-42fa54836dd3
-- statement:
--   Generalization:Let $k\in\mathbb{N^*}$ be a positive integer.Then the equation $x^2+y^2=k^2$ has infinitely many rational solutions.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80396 (k : ℕ) (h : 0 < k) :
  ∀ n : ℕ, ∃ x y : ℚ, x^2 + y^2 = k^2   :=  by sorry
