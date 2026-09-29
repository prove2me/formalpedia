-- Prove2me | Theorems.Thm_lean_workbook_plus_52176
-- name    : lean_workbook_plus_52176
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e1e41108-f7fb-41e6-9d17-783aebe01b82
-- statement:
--   Prove by induction on $n\geqslant 1$ that if $M,N \in \mathbb{R}[x]$ are non constant polynomials with $\deg (M),\deg (N) \leqslant n$ such that $M(x+1)N(x) = M(x)N(x+1)$ for all $x\in \mathbb{R}$, then $M=h\cdot N$ for some real constant $h$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52176 (n : ℕ) (hn : 1 ≤ n) :
    ∀ M N : Polynomial ℝ, M.degree ≤ n ∧ N.degree ≤ n ∧ (∀ x, M.eval (x + 1) * N.eval x = M.eval x * N.eval (x + 1)) → ∃ h : ℝ, M = h • N   :=  by sorry
