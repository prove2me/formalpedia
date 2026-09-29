-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_empirical_row_deviation_at_sample_size_prob_le
-- name    : BanditAlgorithm.mdp_empirical_row_deviation_at_sample_size_prob_le
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-03T02:51:17.930516+00:00
-- url     : https://prove2.me/theorems/ad0eac57-9812-4a57-a606-07f02b77f597
-- title:
--   Weissman $\ell_1$ deviation of the empirical transition row at a fixed sample size
-- statement:
--   Fix a finite MDP $M$ with $S\ge1$ states and $A\ge1$ actions, an initial state distribution, a policy, a horizon $n$, a state-action pair $(s,a)$ and a sample size $m\ge1$. Under the law of the trajectory, for every $\varepsilon\ge0$,
--   $$\mathbb{P}\Big(\exists k\le n:\ N_k(s,a)=m\ \text{ and }\ \sum_{s'}\big|\hat P_k(s'\mid s,a)-P(s'\mid s,a)\big|\ge\varepsilon\Big)\ \le\ 2^{S}e^{-m\varepsilon^{2}/2},$$
--   where $N_k(s,a)$ is the number of transitions out of $(s,a)$ observed before time $k$ and $\hat P_k(\cdot\mid s,a)$ is the corresponding empirical row.
--
--   This is Weissman's $L^1$ deviation inequality applied to the empirical row of a state-action pair at a *fixed sample size*, rather than at a fixed time. The empirical row at time $k$ depends on $k$ only through the number of observations it is built from, so quantifying over the times $k$ at which the count equals $m$ describes a single empirical distribution; the content of the statement is that, conditionally on $(s,a)$ having been visited $m$ times, the $m$ recorded successor states behave as an i.i.d. sample from the true row $P(\cdot\mid s,a)$, even though the visit times are determined by the policy and by the trajectory itself. The bound is uniform in $n$ and in the policy, which is what makes the union bound over pairs and sample sizes in the UCRL2 analysis possible.
--
--   **Formalization note.** No lower bound on the horizon is needed: when $n$ is too small for $(s,a)$ to be visited $m$ times the event is empty. The count `mdpObservedCount h k s a` lags the visit count by one round, because a transition out of $(s,a)$ is recorded only once the following state has been observed.
--
--   Source: Jaksch, Ortner and Auer, *Near-optimal Regret Bounds for Reinforcement Learning*, JMLR 11 (2010), Section 4.1 and Lemma 17 (via Weissman et al., *Inequalities for the L1 deviation of the empirical distribution*, HP Labs tech. report HPL-2003-97).
-- source:
--   Jaksch, Ortner, Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Sec. 4.1 / Lemma 17

import Definitions.Def_UCRL2ConfidenceSets

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_empirical_row_deviation_at_sample_size_prob_le
    (S A n : ℕ) (hS : 0 < S) (hA : 0 < A)
    (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A)
    (s : Fin S) (a : Fin A) (m : ℕ) (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε) :
    (mdpMeasure M μ0 π n).real
        {h | ∃ k ≤ n, mdpObservedCount h k s a = m ∧
              ε ≤ ∑ s', |mdpEmpiricalRow h k s a s' - (M.P s a s' : ℝ)|}
      ≤ 2 ^ S * Real.exp (-(m : ℝ) * ε ^ 2 / 2) := by
  sorry
