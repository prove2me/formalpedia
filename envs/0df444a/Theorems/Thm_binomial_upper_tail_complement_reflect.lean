-- Prove2me | Theorems.Thm_binomial_upper_tail_complement_reflect
-- name    : binomial_upper_tail_complement_reflect
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T21:07:59.972616+00:00
-- url     : https://prove2.me/theorems/37ec7785-09e7-44c2-b659-c95c10706450
-- title:
--   Binomial upper-tail complement via reflection
-- statement:
--   Binomial upper-tail complement via reflection. For $m\le N$ and any real $p$, $$\sum_{k=N-m}^{N}\binom{N}{k}(1-p)^k p^{N-k} \;=\; 1-\sum_{k=m+1}^{N}\binom{N}{k}p^k(1-p)^{N-k}.$$ Equivalently, the high tail of $\mathrm{Bin}(N,1-p)$ starting at $N-m$ equals the complement of the strict upper tail of $\mathrm{Bin}(N,p)$ above $m$. Here `binomialCardinalityProb N k p` $=\binom{N}{k}p^k(1-p)^{N-k}$. Proof combines the reflection $k\leftrightarrow N-k$ (`binomial_tail_reflect`) with the full-sum identity $\sum_{k=0}^N \binom{N}{k}p^k(1-p)^{N-k}=1$ (`binomial_full_sum_eq_one`).
-- source:
--   Standard binomial tail symmetry / complement identity (reindexing $j=N-k$ plus the binomial theorem). Used in Siegel's integer-mean median bound to relate an upper binomial tail to a waiting-time CDF value. A. Siegel, Median Bounds and their Application, J. Algorithms 38, 2001.

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_matrix_completion_fixed_cardinality
open scoped BigOperators
open Finset
open MatrixCompletion

theorem binomial_upper_tail_complement_reflect (N m : ℕ) (h : m ≤ N) (p : ℝ) : (∑ k ∈ Finset.Ico (N-m) (N+1), binomialCardinalityProb N k (1 - p)) = 1 - ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k p := by sorry
