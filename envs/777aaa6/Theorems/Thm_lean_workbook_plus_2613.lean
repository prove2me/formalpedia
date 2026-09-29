-- Prove2me | Theorems.Thm_lean_workbook_plus_2613
-- name    : lean_workbook_plus_2613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/67ffc091-ec61-48cd-9979-db65be2da690
-- statement:
--   $\textbf{Case 1: }$ For $x_1=x_0: x_n=x_0,\;\forall n\in\mathbb{N}$ . In this case, the sequence $(x_n)_{n\in\mathbb{N}}$ is constant, hence convergent.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2613 (x : ℕ → ℝ) (x0 : ℝ) (h : ∀ n, x n = x0) : ∃ l, ∀ ε > 0, ∃ N, ∀ n ≥ N, |x n - l| < ε   :=  by sorry
