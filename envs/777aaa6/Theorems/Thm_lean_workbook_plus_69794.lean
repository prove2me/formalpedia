-- Prove2me | Theorems.Thm_lean_workbook_plus_69794
-- name    : lean_workbook_plus_69794
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/766011e6-2b2b-48ff-a6ce-419074d59e97
-- statement:
--   Prove that there exist an integer $k$ such that $g(x) = f(x+k) \ \ \ \forall x \in \mathbb{R}$ given the conditions $f(x) = a_nx^n + a_{n-1}x^{n-1} + .. + a_1x + a_0$, $g(x) = b_mx^m + b_{m-1}x^{m-1} + .. + b_1x + b_0$, $a_i, b_j \in \mathbb{Z}$ for $0 \le i \le n$ and $0 \le j \le m$, $a_n, b_m > 0$, $n$ is odd, and $\{g(s) | s \in \mathbb{Z}\} = \{f(s) | s \in \mathbb{Z}\}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69794 (n m : ℕ) (a b : ℕ → ℤ) (f g : ℤ → ℤ) (hf: f = ∑ i in Finset.range (n+1), a i * X ^ i) (hg: g = ∑ i in Finset.range (m+1), b i * X ^ i) (ha: a n > 0) (hb: b m > 0) (hn: Odd n) (hm: Odd m) (hZ: Set.range g = Set.range f) : ∃ k : ℤ, ∀ x : ℤ, g x = f (x + k)   :=  by sorry
