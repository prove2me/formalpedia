-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_optimistic_phase_run_on_good_event
-- name    : BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_on_good_event
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T19:57:51.918487+00:00
-- url     : https://prove2.me/theorems/1d0a7bda-ff8d-49cd-9b62-49d6044a55e6
-- title:
--   UCRL2 admits an optimistic phase run on the good event
-- statement:
--   Fix $S\ge2$ states, $A\ge1$ actions, a horizon $n\ge1$, a confidence level $\delta\in(0,1)$ and a known reward function $r$ with values in $[0,1]$.  There is a policy, depending on these known quantities but not on the transition matrix, such that for every communicating MDP $M$ with reward function $r$ and diameter $D(M)\ge1$ and every initial state distribution there is an event $G$ of trajectories with $\mathbb P(G^{c})\le\delta$ on which every trajectory admits an optimistic phase run.
--
--   Call an *optimistic phase run* for a trajectory $h$ of $n$ rounds the following data: a partition of $\{0,\dots,n-1\}$ into consecutive phases $[\tau_k,\tau_{k+1})$, $k<K$, with $\tau_0=0$ and $\tau_K=n$, and for each phase a gain $\rho_k$, a bias $v_k$ and a transition matrix $q_k$, subject to
--
--   1. *few phases*: $K\le 3\sqrt{SAn}$;
--   2. *optimism*: $\rho^{*}\le\rho_k$;
--   3. *span*: $v_k(x)-v_k(y)\le D(M)$ for all states $x,y$;
--   4. *Bellman equation along the trajectory*: $\rho_k+v_k(S_t)=r_{A_t}(S_t)+\langle q_k(S_t),v_k\rangle$ for every round $t$ of phase $k$;
--   5. *estimation error*: $\sum_{k<K}\sum_{t\in[\tau_k,\tau_{k+1})}\langle q_k(S_t)-P_{A_t}(S_t),v_k\rangle\le D(M)(\sqrt2+1)\sqrt{14S\log(2SAn/\delta)}\sqrt{SAn}$;
--   6. *martingale fluctuation*: $\sum_{k<K}\sum_{t\in[\tau_k,\tau_{k+1})}\bigl(\langle P_{A_t}(S_t),v_k\rangle-v_k(S_{t+1})\bigr)\le D(M)\sqrt{2n\log(2/\delta)}$.
--
--   This is the probabilistic half of the analysis of UCRL2 (Lattimore--Szepesvari, Section 38.6).  The policy is UCRL2 itself: it proceeds in phases ended by the doubling criterion, which gives (1); at the start of each phase it plays the memoryless deterministic action map of a solution of the Bellman optimality equation of the extended MDP built from the $\ell^1$ confidence balls, which gives (2), (3) and (4) provided the true transition rows lie in those balls.  The event $G$ is the intersection of the event that they do -- controlled by the categorical concentration inequality together with a union bound over rounds and state-action pairs, and turned into (5) by Hoelder's inequality and the doubling bound on $\sum_k\nu_k/\sqrt{N_k}$ -- with the event that the martingale of (6) does not deviate, controlled by Azuma-Hoeffding.
--
--   **Formalization Note** The states and actions of the trajectory are named by functions on $\mathbb N$ agreeing with $h$ below $n$, so that the terminal state may be supplied as extra data.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5 (the UCRL2 algorithm) and Section 38.6 (Steps 1 and 3 of the proof of Theorem 38.6), with Eq. (38.13) and Lemma 38.8; after Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010), Sections 3 and 4.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_on_good_event
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) :
    ∃ π : MDPPolicy S A,
      ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating → 1 ≤ mdpDiameter M →
        ∀ μ0 : MDPStateDistribution S,
          ∃ G : Set (MDPTrajectory S A n),
            mdpMeasure M μ0 π n Gᶜ ≤ ENNReal.ofReal δ ∧
            ∀ h ∈ G,
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
