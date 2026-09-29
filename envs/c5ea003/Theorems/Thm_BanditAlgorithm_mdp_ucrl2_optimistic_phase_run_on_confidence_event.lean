-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_optimistic_phase_run_on_confidence_event
-- name    : BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_on_confidence_event
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T20:42:00.872681+00:00
-- url     : https://prove2.me/theorems/d0cec747-3be5-42c9-852e-7fa05a52110b
-- title:
--   UCRL2 admits an optimistic phase run on the confidence event
-- statement:
--   Fix $S\ge2$ states, $A\ge1$ actions, a horizon $n\ge1$, a confidence level $\delta\in(0,1)$ and a known reward function $r$ with values in $[0,1]$.  There is a policy, depending on these known quantities but not on the transition matrix, such that for every communicating MDP $M$ with reward function $r$ and diameter $D(M)\ge1$ and every initial state distribution there is an event $E$ with $\mathbb P(E^{c})\le\delta/2$ such that every trajectory lying in $E$ **and** in the confidence good event admits an optimistic phase run.
--
--   Recall that an *optimistic phase run* of a trajectory consists of a partition of the $n$ rounds into consecutive phases $[\tau_k,\tau_{k+1})$, $k<K$, together with a gain $\rho_k$, a bias $v_k$ and a transition matrix $q_k$ per phase, subject to $K\le3\sqrt{SAn}$, optimism $\rho^{*}\le\rho_k$, span $v_k(x)-v_k(y)\le D(M)$, the Bellman equation $\rho_k+v_k(S_t)=r_{A_t}(S_t)+\langle q_k(S_t),v_k\rangle$ along the realised trajectory, and explicit bounds on the accumulated estimation error and martingale fluctuation.
--
--   This is everything in the analysis of UCRL2 (Lattimore--Szepesvari, Sections 38.5 and 38.6) except the concentration of the confidence balls themselves, which is assumed here as membership in `mdpConfidenceGoodEvent`.  The policy is UCRL2: it proceeds in phases ended by the doubling criterion, which gives the bound on $K$; at the start of each phase it plays the memoryless deterministic action map of a solution of the Bellman optimality equation of the extended MDP built from the confidence balls, which gives optimism, the span bound and the Bellman equation as soon as the true rows lie in those balls.  The estimation error is then bounded by Hoelder's inequality against the $\ell^1$ radii together with the doubling bound on $\sum_k\nu_k/\sqrt{N_k}$, and the remaining event $E$ is the one on which the martingale of the run does not deviate, controlled by Azuma--Hoeffding.
--
--   **Formalization Note** The states and actions of the trajectory are named by functions on $\mathbb N$ agreeing with $h$ below $n$, so that the terminal state, which the trajectory does not record but the telescoping and the martingale term refer to, may be supplied as extra data.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5 (the UCRL2 algorithm) and Section 38.6 Steps 2 and 3 with Eq. (38.18)-(38.20), printed pp. 524-528 / PDF pp. 533-537; after Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010), Sections 3 and 4.

import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_on_confidence_event
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) :
    ∃ π : MDPPolicy S A,
      ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating → 1 ≤ mdpDiameter M →
        ∀ μ0 : MDPStateDistribution S,
          ∃ E : Set (MDPTrajectory S A n),
            mdpMeasure M μ0 π n Eᶜ ≤ ENNReal.ofReal (δ / 2) ∧
            ∀ h ∈ mdpConfidenceGoodEvent M n δ ∩ E,
            ∃ (st : ℕ → Fin S) (act : ℕ → Fin A) (K : ℕ) (τ : ℕ → ℕ)
              (ρ : ℕ → ℝ) (v : ℕ → Fin S → ℝ) (q : ℕ → Fin S → Fin S → ℝ),
              (∀ t : Fin n, h t = (st t, act t)) ∧
              τ 0 = 0 ∧ τ K = n ∧ (∀ k, τ k ≤ τ (k + 1)) ∧
              (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) ∧
              (∀ k < K, mdpOptimalGain M ≤ ρ k) ∧
              (∀ k < K, ∀ x y : Fin S, v k x - v k y ≤ mdpDiameter M) ∧
              (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ρ k + v k (st t)
                  = M.r (st t) (act t) + ∑ s', q k (st t) s' * v k s') ∧
              (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
                ≤ mdpDiameter M * (Real.sqrt 2 + 1) *
                    Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
                    Real.sqrt (S * A * n)) ∧
              (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1)))
                ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))) := by
  sorry
