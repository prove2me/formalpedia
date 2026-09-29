-- Prove2me | Theorems.Thm_lean_workbook_plus_49163
-- name    : lean_workbook_plus_49163
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/f37fcc57-e4ae-4924-9d92-5de29d390e30
-- statement:
--   Prove that the sequence $\frac{2n + 1}{n + 1}$ is increasing.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49163 (f : ℕ → ℝ) (n m : ℕ) (h₁ : m > n) (h₂ : f m = (2 * m + 1) / (m + 1)) (h₃ : f n = (2 * n + 1) / (n + 1)) : f m > f n   :=  by sorry
