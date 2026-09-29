-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_measure_map_restrict
-- name    : BanditAlgorithm.mdp_measure_map_restrict
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T04:49:17.815874+00:00
-- url     : https://prove2.me/theorems/95d97007-e77e-4b45-be19-7bc247a636c8
-- title:
--   Truncating a trajectory law to a shorter horizon
-- statement:
--   Let $M$ be a finite MDP, $\pi$ a policy and $\mu_0$ an initial state distribution, and let $\mathbb{P}_n$ denote the law of the trajectory $(S_1,A_1),\dots,(S_n,A_n)$ produced by their interconnection. For $m \le n$, the pushforward of $\mathbb{P}_n$ along the restriction map that keeps only the first $m$ rounds is $\mathbb{P}_m$:
--
--   $$\big(\mathrm{restrict}_{m}\big)_{*}\, \mathbb{P}_n \;=\; \mathbb{P}_m .$$
--
--   In other words the finite-horizon laws of Lattimore and Szepesvári, Figure 38.1, are consistent, so a quantity depending only on the first $m$ rounds has the same expectation at every horizon $n \ge m$. This is what makes it legitimate to compute, inside a single horizon-$n$ expectation, probabilities of events such as "the target state has not been visited during the first $m$ rounds", whose natural home is the horizon-$m$ measure; it is used in that way when the accumulated Bellman inequality is summed against the marginals that define the travel time of Definition 38.1.
--
--   The proof reduces to the one-round case by induction, since restricting from $n+1$ to $m$ is restricting from $n$ to $m$ after forgetting the last round. The one-round case holds because $\mathbb{P}_{n+1}$ is by construction the pushforward along $\mathrm{Fin.snoc}$ of the composition-product of $\mathbb{P}_n$ with the step kernel, and the first marginal of a composition-product with a Markov kernel is the first factor.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 38.1 and Figure 38.1 (the interaction protocol of MDP learning and its finite-horizon laws).

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_measure_map_restrict {S A : ℕ} (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) {m n : ℕ} (hmn : m ≤ n) :
    (mdpMeasure M μ0 π n).map (fun (h : MDPTrajectory S A n) (t : Fin m) ↦
        h (Fin.castLE hmn t))
      = mdpMeasure M μ0 π m := by
  sorry
