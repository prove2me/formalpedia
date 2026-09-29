-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_regret_bound_of_optimistic_phase_run
-- name    : BanditAlgorithm.mdp_ucrl2_regret_bound_of_optimistic_phase_run
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T19:57:41.294477+00:00
-- url     : https://prove2.me/theorems/a784c5b6-060d-4fcc-9913-1a63a13c47b6
-- title:
--   Regret bound for any trajectory admitting an optimistic phase run
-- statement:
--   There is a universal constant $C>0$ such that, for every MDP $M$ with $S\ge2$ states, $A\ge1$ actions and diameter $D(M)\ge1$, every horizon $n\ge1$, every $\delta\in(0,1)$ and every trajectory $h$ of $n$ rounds admitting an optimistic phase run, the regret satisfies
--   $$\widehat R_n(h) < C\, D(M)\, S\sqrt{An\log(nSA/\delta)}.$$
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
--   This is the deterministic half of the analysis of UCRL2 (Lattimore--Szepesvari, Section 38.6): no probability appears, the whole argument being the per-phase telescoping of the Bellman equation, which turns the regret into the sum of the three quantities bounded in (3), (5) and (6), followed by the arithmetic that collects them into the stated bound.
--
--   **Formalization Note** The states and actions of the trajectory are named by functions on $\mathbb N$ agreeing with $h$ below $n$; this lets the terminal state $S_n$, which the trajectory does not record but the telescoping and the martingale term refer to, be an unconstrained extra datum.  The hypothesis $S\ge2$ is not a restriction: a one-state MDP has empty diameter supremum, hence $D(M)=0$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.6, Eq. (38.18)-(38.20) and the display collecting the three terms; after Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010), Section 4.

import Definitions.Def_FiniteMDPLearning
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_ucrl2_regret_bound_of_optimistic_phase_run :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, 2 ≤ S → 0 < A → 0 < n →
        ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
          ∀ M : FiniteMDP S A, 1 ≤ mdpDiameter M →
            ∀ (h : MDPTrajectory S A n) (st : ℕ → Fin S) (act : ℕ → Fin A),
              (∀ t : Fin n, h t = (st t, act t)) →
              ∀ (K : ℕ) (τ : ℕ → ℕ) (ρ : ℕ → ℝ) (v : ℕ → Fin S → ℝ)
                (q : ℕ → Fin S → Fin S → ℝ),
                τ 0 = 0 → τ K = n → (∀ k, τ k ≤ τ (k + 1)) →
                (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) →
                (∀ k < K, mdpOptimalGain M ≤ ρ k) →
                (∀ k < K, ∀ x y : Fin S, v k x - v k y ≤ mdpDiameter M) →
                (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ρ k + v k (st t)
                    = M.r (st t) (act t) + ∑ s', q k (st t) s' * v k s') →
                (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                    ∑ s', (q k (st t) s' - (M.P (st t) (act t) s' : ℝ)) * v k s'
                  ≤ mdpDiameter M * (Real.sqrt 2 + 1) *
                      Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)) *
                      Real.sqrt (S * A * n)) →
                (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                    ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1)))
                  ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))) →
                mdpRegret M n h <
                  C * mdpDiameter M * S *
                    Real.sqrt (A * n * Real.log (n * S * A / δ)) := by
  sorry
