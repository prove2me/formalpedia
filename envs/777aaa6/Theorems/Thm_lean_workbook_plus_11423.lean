-- Prove2me | Theorems.Thm_lean_workbook_plus_11423
-- name    : lean_workbook_plus_11423
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/52056717-c2bf-4e95-908e-b65ad1690af8
-- statement:
--   Let $x_1 \in <0,1>$ and define $x_{n+1}=x_n +\frac{x_{n}^{2}}{n^2}$ . Prove that the sequence $x_n$ is bounded.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11423 (x : ℕ → ℝ) (hx: ∀ n, 0 < x n ∧ x n < 1) (hn: ∀ n, x (n + 1) = x n + (x n)^2 / n^2): ∃ M, ∀ n, abs (x n) < M   :=  by sorry
