-- Prove2me | Theorems.Thm_lean_workbook_plus_9417
-- name    : lean_workbook_plus_9417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2b4212c4-9b18-462e-9ee5-75673596be6a
-- statement:
--   For pointwise convergence, does $f_n(x)$ converge to a limit function $f(x)$ for every $x \in \mathbb{R}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9417 (f : ℕ → ℝ → ℝ) (f_lim : ℝ → ℝ) (hf : ∀ x, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n x - f_lim x| < ε) : ∀ x, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n x - f_lim x| < ε   :=  by sorry
