-- Prove2me | Theorems.Thm_finite_rademacher_weighted_first_moment_le_even_moment_root
-- name    : finite_rademacher_weighted_first_moment_le_even_moment_root
-- status  : Proved
-- author  : @Minghui
-- created : 2026-06-25T20:24:50.105024+00:00
-- url     : https://prove2.me/theorems/e5c34bb4-765a-4e15-a61d-f1a7b1201816
-- statement:
--   This is a formal bridge for the finite Rademacher power-mean step used in the Rudelson/Lust-Picquard noncommutative-Khintchine route.
--
--   Source: Candes--Recht, *Exact Matrix Completion via Convex Optimization*, PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9), where the tangent-sampling expectation is controlled by Rudelson's selection estimate; Rudelson, *Random vectors in the isotropic position*, JFA 164 (1999), Theorem 1, proof Steps 1--2; and Hardy--Littlewood--Polya, *Inequalities*, Section 2.10, for power means.
--
--   Mathematical statement. Let $iota$ be a finite Rademacher index set and let $F(eps) >= 0$ be a nonnegative statistic on sign subsets $eps : Finset iota$. For every integer $q >= 1$,
--   $$
--   sum_eps 2^(-|iota|) F(eps) <= (sum_eps 2^(-|iota|) F(eps)^(2q))^(1/(2q)).
--   $$
--
--   Variables and notation. This node uses the auxiliary Rademacher probability model: each sign pattern is represented by a subset $eps subset iota$ and has weight $2^(-|iota|)$. In the downstream Candes--Recht application, $n = max(n_1,n_2)$, $p = m/(n_1 n_2)$ is the Bernoulli sampling rate, $Omega$ is a fixed Bernoulli sample realization, and $F(eps) = ||sum_c eps_c H_c||$ for Hermitian matrices $H_c$.
--
--   Formalization note. This is a formal bridge. It does not appear verbatim in Candes--Recht. It bridges the proved source-backed power-mean node `rademacher_expectation_power_mean` (`9a9634f8`) and the source-backed child route through `rademacher_matrix_operator_norm_first_moment_log_window_from_2p` (`136263d8`) toward `inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max` (`f4806ebd`).
-- source:
--   Candes--Recht, Exact Matrix Completion via Convex Optimization, PDF p. 19, Section 4.2, Theorem 4.2, equation (4.9); Rudelson, Random vectors in the isotropic position, JFA 164 (1999), Theorem 1, proof Steps 1--2; Hardy--Littlewood--Polya, Inequalities, Section 2.10.

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Classical BigOperators

theorem finite_rademacher_weighted_first_moment_le_even_moment_root :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (F : Finset ι → ℝ), (∀ eps, 0 ≤ F eps) →
      ∀ p : ℕ, 1 ≤ p →
      (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) * F eps)
        ≤ (∑ eps : Finset ι,
            ((1 : ℝ) / 2) ^ (Fintype.card ι) * (F eps) ^ (2 * p))
            ^ ((1 : ℝ) / (2 * p)) := by
  sorry
