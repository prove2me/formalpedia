-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_optimistic_phase_run_with_confidence_widths
-- name    : BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_with_confidence_widths
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T21:13:47.566584+00:00
-- url     : https://prove2.me/theorems/549fef42-a195-4d06-b896-a6840423cfb7
-- title:
--   UCRL2 optimistic phase run with explicit confidence widths
-- statement:
--   Fix $S\ge2$ states, $A\ge1$ actions, a horizon $n\ge1$, a confidence level $\delta\in(0,1)$ and a known reward function $r$ with values in $[0,1]$.  There is a policy, depending on these known quantities but not on the transition matrix, such that for every communicating MDP $M$ with reward function $r$ and diameter $D(M)\ge1$ and every initial state distribution there is an event $E$ with $\mathbb P(E^{c})\le\delta/2$ such that every trajectory lying in $E$ and in the confidence good event admits an *optimistic phase run reporting its confidence widths*.
--
--   This is the run of UCRL2 with its bookkeeping left visible.  As in the plain optimistic phase run, the $n$ rounds are cut into consecutive phases $[\tau_k,\tau_{k+1})$, $k<K$, with $K\le3\sqrt{SAn}$, and each phase $k$ carries a gain $\rho_k$, a bias $v_k$ and a transition matrix $q_k$ satisfying optimism $\rho^{*}\le\rho_k$, the span bound $v_k(x)-v_k(y)\le D(M)$ and the Bellman equation $\rho_k+v_k(S_t)=r_{A_t}(S_t)+\langle q_k(S_t),v_k\rangle$ along the realised trajectory.  What is reported in addition is the data that the accumulated estimation error is computed from:
--
--   - the visit counts $N_k(s,a)$ at the start of phase $k$ and the numbers $\nu_k(s,a)$ of visits during it, satisfying $N_0=0$, $N_{k+1}=N_k+\nu_k$, $\nu_k\ge0$, the *doubling inequality* $\nu_k(s,a)\le\max(1,N_k(s,a))$ that is exactly what ends a phase, and $\sum_{s,a}N_K(s,a)\le n$;
--   - the fact that summing any function of the pair over the rounds of phase $k$ is the same as summing it against $\nu_k$;
--   - the *width* bound: the optimistic row $q_k(S_t,\cdot)$ and the true row $P_{A_t}(S_t,\cdot)$ both lie in the confidence ball of the pair played, hence are within $2\sqrt{14S\log(2SAn/\delta)/\max(1,N_k(S_t,A_t))}$ of each other in $\ell^1$;
--   - each $q_k(s,\cdot)$ is a probability vector.
--
--   Everything except the accumulated estimation error is stated exactly as in the plain optimistic phase run; the estimation error is replaced by these local facts, which is what the algorithm actually delivers and from which the aggregate bound is a computation.
--
--   **Formalization Note** The states and actions of the trajectory are named by functions on $\mathbb N$ agreeing with $h$ below $n$, so that the terminal state, which the trajectory does not record but the telescoping and the martingale term refer to, may be supplied as extra data.  The counts are real-valued because that is the form in which the doubling sum is applied.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5 (the UCRL2 algorithm, and the doubling stopping rule for a phase) and Section 38.6 Steps 2 and 3, printed pp. 524-528 / PDF pp. 533-537; after Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010), Sections 3 and 4.

import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_with_confidence_widths
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
              (ρ : ℕ → ℝ) (v : ℕ → Fin S → ℝ) (q : ℕ → Fin S → Fin S → ℝ)
              (N ν : ℕ → Fin S → Fin A → ℝ),
              (∀ t : Fin n, h t = (st t, act t)) ∧
              τ 0 = 0 ∧ τ K = n ∧ (∀ k, τ k ≤ τ (k + 1)) ∧
              (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) ∧
              (∀ k < K, mdpOptimalGain M ≤ ρ k) ∧
              (∀ k < K, ∀ x y : Fin S, v k x - v k y ≤ mdpDiameter M) ∧
              (∀ k < K, ∀ s : Fin S, ∑ s', q k s s' = 1) ∧
              (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ρ k + v k (st t)
                  = M.r (st t) (act t) + ∑ s', q k (st t) s' * v k s') ∧
              (∀ s a, N 0 s a = 0) ∧
              (∀ k s a, 0 ≤ ν k s a) ∧
              (∀ k s a, N (k + 1) s a = N k s a + ν k s a) ∧
              (∀ k s a, ν k s a ≤ max 1 (N k s a)) ∧
              (∑ s, ∑ a, N K s a ≤ (n : ℝ)) ∧
              (∀ k < K, ∀ g : Fin S → Fin A → ℝ,
                ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)), g (st t) (act t)
                  = ∑ s, ∑ a, ν k s a * g s a) ∧
              (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ∑ s', |q k (st t) s' - (M.P (st t) (act t) s' : ℝ)|
                  ≤ 2 * Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)
                      / max 1 (N k (st t) (act t)))) ∧
              (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1)))
                ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))) := by
  sorry
