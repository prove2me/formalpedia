-- Prove2me | Theorems.Thm_lean_workbook_plus_81405
-- name    : lean_workbook_plus_81405
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/adbd7755-fcc8-4518-9d15-6381876978a9
-- statement:
--   Since $x_n^2$ is the highest square, all other $x_i^2$ are in $[-x_n^2, x_n^2]$, so each $x_i$ is in $[-|x_n|, |x_n|]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81405  (x : ℕ → ℝ)
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ i, 0 ≤ x i)
  (h₂ : ∀ i, x i^2 ≤ x n^2) :
  ∀ i, -|x n| ≤ x i ∧ x i ≤ |x n|   :=  by sorry
