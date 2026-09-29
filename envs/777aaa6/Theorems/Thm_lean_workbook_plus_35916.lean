-- Prove2me | Theorems.Thm_lean_workbook_plus_35916
-- name    : lean_workbook_plus_35916
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/89c60857-4a1d-4873-9108-08e5f1d40b31
-- statement:
--   Prove that if a function $g:\mathbb{R}\to\mathbb{R}$ is super-Lipschitz, it is constant (Proof #1).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35916 ∀ g : ℝ → ℝ, (∀ x y : ℝ, |g x - g y| ≤ |x - y|) → ∃ c :ℝ, ∀ x : ℝ, g x = c   :=  by sorry
