-- Prove2me | Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_mertens_bound_ascii
-- name    : moebius_dirichlet_partialSum_tendsto_of_mertens_bound_ascii
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-03T13:54:48.203088+00:00
-- url     : https://prove2.me/theorems/fd6087ed-6202-479b-8f47-0d9a6254bd6b
-- title:
--   Mertens growth implies convergence of the real Mobius Dirichlet series
-- statement:
--   Assume that for every positive epsilon, the Mobius summatory function M(N), the sum of mu(n) for 1 <= n <= N, is O(N^(1/2+epsilon)). Then for every real sigma > 1/2, the real Dirichlet series with terms mu(n) n^(-sigma) converges. Partial summation reduces this to integrability at infinity after choosing epsilon < sigma - 1/2.
-- source:
--   Abel summation applied to the Mertens growth criterion; compare Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed. (1986), section 14.25(C), equation (14.25.2), p. 370.

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff

theorem moebius_dirichlet_partialSum_tendsto_of_mertens_bound_ascii
    (sigma : Real) (hsigma : 1 / 2 < sigma)
    (hM : forall epsilon : Real, 0 < epsilon ->
      Asymptotics.IsBigO Filter.atTop
        (fun N : Nat => Finset.sum (Finset.Icc 1 N)
          (fun n => (ArithmeticFunction.moebius n : Complex)))
        (fun N : Nat => (N : Real) ^ (1 / 2 + epsilon))) :
    Exists fun L : Real => Filter.Tendsto
      (fun N : Nat => Finset.sum (Finset.Icc 1 N)
        (fun n => (ArithmeticFunction.moebius n : Real) * (n : Real) ^ (-sigma)))
      Filter.atTop (nhds L) := by sorry
