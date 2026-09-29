-- Prove2me | Theorems.Thm_lean_workbook_plus_24990
-- name    : lean_workbook_plus_24990
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/2c39b112-bf19-4692-8652-f8f717f6de9e
-- statement:
--   Prove the given lemma: $ x_n$ is a Cauchy sequence in $ X$ if and only if for any $ \epsilon > 0$, there exists $ N$ such that for all $ n \geq N$, $ \rho(x_n, x_N) < \epsilon$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24990 (X : Type*) [MetricSpace X] (x : ℕ → X) :
  CauchySeq x ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x n) (x N) < ε   :=  by sorry
