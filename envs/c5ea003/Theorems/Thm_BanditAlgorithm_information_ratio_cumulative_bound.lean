-- Prove2me | Theorems.Thm_BanditAlgorithm_information_ratio_cumulative_bound
-- name    : BanditAlgorithm.information_ratio_cumulative_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T20:43:10.949248+00:00
-- url     : https://prove2.me/theorems/ea31b532-dff3-4a7f-add6-23b919ffa9b8
-- title:
--   Finite-horizon information-ratio cumulative bound
-- statement:
--   Let $n$ be a finite horizon. For every round $t$, let $\delta_t\ge 0$ be an instantaneous regret and let $I_t\ge 0$ be the corresponding information gain. Suppose $\Gamma,H\ge 0$, the pointwise information-ratio inequalities
--
--   $$
--   \delta_t^2\le \Gamma I_t
--   $$
--
--   hold for all $t$, and the total information satisfies $\sum_{t=1}^n I_t\le H$. Then
--
--   $$
--   \sum_{t=1}^n \delta_t\le \sqrt{n\Gamma H}.
--   $$
--
--   This is the reusable finite-sum Cauchy--Schwarz step in the information-ratio method for Bayesian regret.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Theorem 36.6, printed pp. 470-471, especially the Cauchy-Schwarz calculation in Eq. (36.10).

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

theorem BanditAlgorithm.information_ratio_cumulative_bound {n : ℕ}
    (δ info : Fin n → ℝ) (Γ H : ℝ)
    (hδ : ∀ t, 0 ≤ δ t) (hinfo : ∀ t, 0 ≤ info t)
    (hΓ : 0 ≤ Γ) (hH : 0 ≤ H)
    (hpoint : ∀ t, δ t ^ 2 ≤ Γ * info t)
    (hsum : ∑ t, info t ≤ H) :
    ∑ t, δ t ≤ Real.sqrt (n * Γ * H) := by
  sorry
