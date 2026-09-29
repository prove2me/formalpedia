-- Prove2me | Theorems.Thm_lean_workbook_plus_15911
-- name    : lean_workbook_plus_15911
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/88fd259d-51f1-4741-a5c9-992e5f2d6c56
-- statement:
--   If $f:\mathbb{R}\to\mathbb{R}$ is an infinitely differentiable function with the property that there is $n\in\mathbb{N}$ such that for every $x\in\mathbb{R}$ , $f^{(n)}(x) = 0$ ( $n$ -th derivative), then $f$ is a polynomial.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15911 (f : ℝ → ℝ) (hf : ∃ n : ℕ, ∀ x : ℝ, (f x)^(n) = 0) : ∃ p : Polynomial ℝ, ∀ x : ℝ, f x = p.eval x   :=  by sorry
