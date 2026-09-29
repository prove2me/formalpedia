-- Prove2me | Theorems.Thm_lean_workbook_plus_60636
-- name    : lean_workbook_plus_60636
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e6e5a2d4-0372-417d-8758-679954f2bd22
-- statement:
--   Prove the Nested Interval Theorem: if $I_n=[a_n,b_n]$ are a sequence of closed bounded intervals such that $I_1\supseteq I_2\subseteq I_3\supseteq\cdots,$ then $\bigcup_{n=1}^{\infty}I_n$ is nonempty.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60636 (a b : ℕ → ℝ) (hab : ∀ n, a n ≤ b n) (h1 : ∀ n, [a n, b n] ⊆ [a (n + 1), b (n + 1)]): ∃ x, ∀ n, x ∈ [a n, b n]   :=  by sorry
