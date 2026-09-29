-- Prove2me | Theorems.Thm_binomial_tail_reflect
-- name    : binomial_tail_reflect
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T20:34:44.730711+00:00
-- url     : https://prove2.me/theorems/5cc554a3-4841-479a-b8bc-5ccd216c7eca
-- title:
--   Binomial upper-tail reflection $k\leftrightarrow N-k$
-- statement:
--   **Binomial upper-tail reflection ($k\leftrightarrow N-k$).** For $m\le N$ and any real $q$, $$\sum_{k=N-m}^{N}\binom{N}{k}q^k(1-q)^{N-k}=\sum_{j=0}^{m}\binom{N}{j}(1-q)^j q^{N-j}.$$ Substituting $j=N-k$ (with $\binom{N}{k}=\binom{N}{N-k}$) turns the high tail of $\mathrm{Bin}(N,q)$ into the low tail of $\mathrm{Bin}(N,1-q)$. Combined with the full-sum identity this expresses an upper binomial tail as one minus a complementary lower tail — the failure-reversal bridge.
-- source:
--   Elementary binomial tail symmetry P(Bin(N,q)≥N-m)=P(Bin(N,1-q)≤m); proof = reindex j=N-k + Nat.choose_symm. Used in the Siegel/Jogdeo-Samuels integer-mean binomial median argument (failure reversal).

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open scoped BigOperators
open Finset

theorem binomial_tail_reflect (N m : ℕ) (hm : m ≤ N) (q : ℝ) : (∑ k ∈ Finset.Ico (N-m) (N+1), (Nat.choose N k : ℝ) * q ^ k * (1 - q) ^ (N - k)) = ∑ j ∈ Finset.range (m+1), (Nat.choose N j : ℝ) * (1 - q) ^ j * q ^ (N - j) := by sorry
