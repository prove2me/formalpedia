-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_ucrl2_good_event_regret_bound
-- name    : BanditAlgorithm.mdp_ucrl2_good_event_regret_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T19:44:12.942905+00:00
-- url     : https://prove2.me/theorems/c9438726-5e2d-48ca-84a7-541d351a0275
-- title:
--   UCRL2 regret bound on the good event
-- statement:
--   There is a universal constant $C>0$ with the following property.  Fix positive numbers of states $S$, actions $A$, and rounds $n$, a confidence level $\delta\in(0,1)$, and a known reward function $r:\mathcal S\times\mathcal A\to[0,1]$.  There is a policy, depending on these known quantities but not on the transition matrix, such that for every communicating MDP $M$ with reward function $r$, diameter $D(M)\ge1$, and every initial state distribution, there is an event $G$ of trajectories with
--   $$\mathbb P(G^{c})\le\delta \qquad\text{and}\qquad \widehat R_n < C D(M) S\sqrt{An\log(nSA/\delta)}\ \text{ on } G.$$
--
--   This is the form in which the analysis of UCRL2 (Lattimore--Szepesvari, Section 38.6) actually delivers Theorem 38.6: the event $G$ is the event that the true transition rows lie in every confidence ball built along the trajectory, its complement is controlled by a concentration argument, and the regret bound on $G$ is a deterministic consequence of optimism.  Separating the two makes the probabilistic and the deterministic halves of the proof independent.
--
--   **Formalization Note** The regret bound on $G$ is stated with a strict inequality, matching the source, so that the bad event of Theorem 38.6 is contained in $G^{c}$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Theorem 38.6, printed p. 523 / PDF p. 532, and its proof in Section 38.6; known-reward standing assumption in Sections 38.4--38.5.

import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.mdp_ucrl2_good_event_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
        ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
          ∀ r : Fin S → Fin A → ℝ, (∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) →
            ∃ π : MDPPolicy S A,
              ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating →
                1 ≤ mdpDiameter M →
                ∀ μ0 : MDPStateDistribution S,
                  ∃ G : Set (MDPTrajectory S A n),
                    mdpMeasure M μ0 π n Gᶜ ≤ ENNReal.ofReal δ ∧
                    ∀ h ∈ G, mdpRegret M n h <
                      C * mdpDiameter M * S *
                        Real.sqrt (A * n * Real.log (n * S * A / δ)) := by
  sorry
