-- Prove2me | Theorems.Thm_binomial_upper_tail_eq_incomplete_beta
-- name    : binomial_upper_tail_eq_incomplete_beta
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T14:17:11.02977+00:00
-- url     : https://prove2.me/theorems/555e60ad-728b-45f8-85e1-512de469d96f
-- title:
--   Binomial upper tail as an incomplete Beta integral
-- statement:
--   For a binomial distribution $\mathrm{Bin}(N,p)$ with $0 \le m < N$, the strict upper tail probability equals an incomplete Beta integral:
--   $$\sum_{k=m+1}^{N} \binom{N}{k} p^k (1-p)^{N-k} = \int_0^p N\binom{N-1}{m} t^m (1-t)^{N-1-m}\, dt.$$
--   This is the classical binomial-tail / regularized-incomplete-beta identity, proved by the Fundamental Theorem of Calculus: the derivative of the tail polynomial $g(p)=\sum_{k=m+1}^N \binom{N}{k}p^k(1-p)^{N-k}$ telescopes to the single term $N\binom{N-1}{m}p^m(1-p)^{N-1-m}$, and $g(0)=0$. Here `binomialCardinalityProb N k p` denotes $\binom{N}{k}p^k(1-p)^{N-k}$ and `Finset.Ioo m (N+1)` is the index set $\{m+1,\dots,N\}$.
-- source:
--   https://en.wikipedia.org/wiki/Binomial_distribution#Tail_bounds

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_matrix_completion_fixed_cardinality
open scoped BigOperators
open Finset
open MatrixCompletion

theorem binomial_upper_tail_eq_incomplete_beta (N m : ℕ) (h : m < N) (p : ℝ) :
    ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k p
      = ∫ t in (0:ℝ)..p, (N : ℝ) * (Nat.choose (N-1) m : ℝ) * t ^ m * (1 - t) ^ (N - 1 - m) := by sorry
