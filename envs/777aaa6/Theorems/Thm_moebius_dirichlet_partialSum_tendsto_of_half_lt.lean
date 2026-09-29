-- Prove2me | Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_half_lt
-- name    : moebius_dirichlet_partialSum_tendsto_of_half_lt
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-10T19:51:45.76681+00:00
-- url     : https://prove2.me/theorems/b79e896e-0e10-43f7-bdeb-439d74d3f596
-- title:
--   Convergence of the Moebius Dirichlet series at every real abscissa above $1/2$
-- statement:
--   Let $\mu$ be the Moebius function. For a real number $\sigma>\tfrac12$ the assertion is that the Dirichlet series of $\mu$ converges at $\sigma$, that is, the sequence of partial sums
--
--   $$S_N(\sigma)=\sum_{n=1}^{N}\frac{\mu(n)}{n^{\sigma}}$$
--
--   has a finite limit as $N\to\infty$.
--
--   Convergence of $\sum_{n\ge1}\mu(n)n^{-s}$ throughout the half-plane $\operatorname{Re} s>\tfrac12$ is one of the standard equivalent forms of the Riemann Hypothesis (Titchmarsh and Heath-Brown, Theorem 14.25(A)); the present statement is its restriction to real $s=\sigma$, which is already equivalent to it. Indeed, convergence at every real $\sigma>\tfrac12$ forces the Mertens function to satisfy $M(x)=O(x^{\sigma})$ for every such $\sigma$ by partial summation, and that bound in turn yields the zero-free half-plane $\operatorname{Re} s>\tfrac12$. The assertion is therefore open.
--
--   Unconditionally the series converges for $\sigma>1$, where it equals $1/\zeta(\sigma)$, and the content of the statement is the range $\tfrac12<\sigma\le1$: it asserts exactly the cancellation in the sequence $\mu(1),\mu(2),\dots$ that the Riemann Hypothesis predicts.
--
--   **Formalization Note.** Convergence is expressed as the existence of a real number $L$ such that the partial sums over $1\le n\le N$ tend to $L$ along `atTop`. The summands are real; the coefficient $\mu(n)$ is the integer value of Mathlib's `ArithmeticFunction.moebius` cast to $\mathbb R$, and $n^{-\sigma}$ is the real power `(n : ℝ) ^ (-σ)`.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, Section 14.25, Theorem 14.25(A), p. 370 (the series form of the criterion, restricted to real s).

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

theorem moebius_dirichlet_partialSum_tendsto_of_half_lt (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      Filter.atTop (nhds L) := by sorry
