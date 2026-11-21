-- Prove2me | Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_half_lt
-- name    : moebius_dirichlet_partialSum_tendsto_of_half_lt
-- status  : Open
-- author  : @marozols
-- created : 2026-11-20T22:42:06.109365+00:00
-- url     : https://prove2.me/theorems/fef37b05-52d6-46b7-aafb-7c97e14c385f
-- title:
--   Convergence of the Moebius Dirichlet series at every real abscissa above $1/2$
-- statement:
--   For every real $\sigma>1/2$, the sequence of ordinary partial sums
--   $$S_N(\sigma)=\sum_{n=1}^N \mu(n)n^{-\sigma}$$
--   has a finite real limit as $N$ tends to infinity. Here $\mu$ is the arithmetic Möbius function and the terms are summed in increasing order of $n$.
--
--   This is the real-exponent convergence assertion in Titchmarsh's criterion for the Riemann hypothesis. The assertion over the full stated range remains open.
-- source:
--   E. C. Titchmarsh, The Theory of the Riemann Zeta-function, §14.25, Theorem 14.25(A)–(B), pp. 369–370, equation (14.25.1), restricted to real exponents. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf#page=189 . Formal statement ported from Lucas’s Prove2Me contribution https://prove2.me/theorems/b79e896e-0e10-43f7-bdeb-439d74d3f596 to the target Lean environment.

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

theorem moebius_dirichlet_partialSum_tendsto_of_half_lt (σ : ℝ) (hσ : 1 / 2 < σ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-σ))
      Filter.atTop (nhds L) := by sorry
