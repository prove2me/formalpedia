-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_phase_schedule_from_doubling_rule
-- name    : BanditAlgorithm.mdp_ucrl2_phase_schedule_from_doubling_rule
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T23:14:08.552428+00:00
-- url     : https://prove2.me/theorems/d8edc335-aa1e-4c02-b730-132687553e47
-- title:
--   The UCRL2 doubling rule generates a valid phase schedule
-- statement:
--   Fix $S\ge1$ states, $A\ge1$ actions, a horizon $n\ge1$ and a trajectory $h$ of $n$ rounds. The phase-start map of UCRL2 -- a new phase begins at time $u+1$ as soon as the number of visits to some pair since the start of the current phase has reached $\max(1,N)$, where $N$ is the number of visits accumulated to that pair before the phase began -- cuts $\{0,\dots,n-1\}$ into finitely many consecutive nonempty phases: there are a number $K$ of phases and a nondecreasing sequence of times $\tau_0=0<\tau_1<\dots<\tau_K=n$, stationary at $n$ beyond $K$, such that
--
--   - every time $u$ in $[\tau_k,\tau_{k+1})$ has $\tau_k$ as the start of its phase;
--   - the doubling inequality holds: for $k<K$ and every pair $(s,a)$, the visits to $(s,a)$ before $\tau_{k+1}$ number at most $N_k(s,a)+\max(1,N_k(s,a))$, where $N_k(s,a)$ counts the visits before $\tau_k$ -- no pair is visited during a phase more often than it had been visited before it;
--   - $K\le3\sqrt{SAn}$.
--
--   The last bound is the combinatorial heart of the algorithm: each of the $SA$ pairs can trigger the end of a phase only after its count has doubled, so it triggers at most $\log_2$ of its final count many phases, and Jensen's inequality over the pairs turns the sum of those logarithms into $\sqrt{SAn}$.
--
--   **Formalization Note** The doubling inequality is stated with an addition rather than a truncated subtraction, which is the same statement for natural numbers and avoids the cutoff.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.5 and the phase-counting step of Section 38.6, printed pp. 524-527 / PDF pp. 533-536; Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010), Section 3 and Proposition 18.

import Definitions.Def_UCRL2Algorithm

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_ucrl2_phase_schedule_from_doubling_rule
    (S A n : ℕ) (hS : 0 < S) (hA : 0 < A) (hn : 0 < n)
    (h : MDPTrajectory S A n) :
    ∃ (K : ℕ) (τ : ℕ → ℕ),
      τ 0 = 0 ∧ τ K = n ∧ (∀ k, τ k ≤ τ (k + 1)) ∧
      (∀ k < K, τ k < τ (k + 1)) ∧
      (∀ k, K ≤ k → τ k = n) ∧
      (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) ∧
      (∀ k < K, ∀ u ∈ Finset.Ico (τ k) (τ (k + 1)), mdpPhaseStart h u = τ k) ∧
      (∀ k < K, ∀ (s : Fin S) (a : Fin A),
        mdpVisitCount h (τ (k + 1)) s a
          ≤ mdpVisitCount h (τ k) s a + max 1 (mdpVisitCount h (τ k) s a)) := by
  sorry
