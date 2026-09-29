-- Prove2me | Theorems.Thm_markov_entanglement_decomposition_error
-- name    : markov_entanglement_decomposition_error
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-07-12T05:29:26.256634+00:00
-- url     : https://prove2.me/theorems/0f20fadf-67ca-439c-8746-0ae85098e742
-- title:
--   Markov entanglement bounds the Q-value decomposition error (Thm. 4)
-- statement:
--   Consider a two-agent Markov decision process with a joint transition matrix $P_{AB}$ on the product of the agents' local state-action spaces, a strictly positive stationary occupancy measure mu for $P_{AB}$, a discount factor gamma in $[0,1)$, and local rewards $r_A, r_B$ bounded by $r_A^{\max}, r_B^{\max}$ respectively. Let $P_A^\pi$ and $P_B^\pi$ be the local ('marginalized') transition matrices of agents $A$ and $B$ induced by $P_{AB}$ and mu (Eq. 2 of the source paper), and let $Q_{AB}^\pi, Q_A^\pi, Q_B^\pi$ be the corresponding global and local Q-value functions, each defined as the fixed point of its Bellman equation. Let $P_A$ and $P_B$ be transition matrices that achieve the measure of Markov entanglement of $P_{AB}$ with respect to agent $A$ and agent $B$, respectively, under the agent-wise total variation distance (Eq. 5).
--
--   Then:
--
--   (1) the total variation distance from $P^\pi_A$ to $P_A$ is at most the measure of Markov entanglement of $P_{AB}$ with respect to agent $A$, and symmetrically for agent $B$;
--
--   (2) the entrywise (sup-norm) decomposition error between the global Q-value $Q^\pi_{AB}$ and the sum of the local Q-values $Q^\pi_A + Q^\pi_B$ is at most $4*gamma*(E_A(P_{AB})*r_A^{\max} + E_B(P_{AB})*r_B^{\max}) / (1-gamma)^2$, where $E_A, E_B$ denote the measures of Markov entanglement of $P_{AB}$ with respect to agent A, B.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Section 5.2, p. 16, Theorem 4

import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

/--
Theorem 4 (Chen and Peng, "Multi-agent Markov Entanglement", arXiv:2506.02385v3, Section 5.2,
p. 16). Consider a two-agent MDP with joint transition matrix `P_AB`, occupancy measure `μ`
(strictly positive and stationary for `P_AB`), discount factor `γ ∈ [0, 1)`, and bounded local
rewards `r_A`, `r_B` with bounds `rAmax`, `rBmax`. Let `P_true_A`, `P_true_B` be agent `A`'s and
`B`'s local ("marginalized") transitions induced by `P_AB` and `μ` via Eq. (2), and let `Q_AB`,
`Q_true_A`, `Q_true_B` be the corresponding Q-values, i.e. the fixed points of their Bellman
equations. Let `P_A`, `P_B` be transition matrices achieving the measure of Markov entanglement
of `P_AB` with respect to agent `A`, `B` under the agent-wise total variation distance (Eq. 5).

Then the (ordinary) total variation distance from each agent's true local transition to its
closest independent approximation is bounded by the corresponding measure of Markov
entanglement, and the entrywise decomposition error of the global Q-value against the sum of
local Q-values is bounded by a combination of both measures of Markov entanglement, weighted by
the local reward bounds and scaled by `4γ / (1 - γ)²`.
-/
theorem markov_entanglement_decomposition_error
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P_AB : Matrix (SA × SB) (SA × SB) ℝ) (hP_AB : IsTransitionMatrix P_AB)
    (μ : SA × SB → ℝ) (hμ : IsPositiveDist μ) (hμStat : IsStationary P_AB μ)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r_A : SA → ℝ) (r_B : SB → ℝ) (rAmax rBmax : ℝ)
    (hrAmax : 0 ≤ rAmax) (hrBmax : 0 ≤ rBmax)
    (hrA : ∀ a, |r_A a| ≤ rAmax) (hrB : ∀ b, |r_B b| ≤ rBmax)
    (P_true_A : Matrix SA SA ℝ) (hP_true_A_tm : IsTransitionMatrix P_true_A)
    (hP_true_A : IsLocalTransitionA P_AB μ P_true_A)
    (P_true_B : Matrix SB SB ℝ) (hP_true_B_tm : IsTransitionMatrix P_true_B)
    (hP_true_B : IsLocalTransitionB P_AB μ P_true_B)
    (Q_AB : SA × SB → ℝ) (hQ_AB : IsBellmanQ P_AB (fun p => r_A p.1 + r_B p.2) γ Q_AB)
    (Q_true_A : SA → ℝ) (hQ_true_A : IsBellmanQ P_true_A r_A γ Q_true_A)
    (Q_true_B : SB → ℝ) (hQ_true_B : IsBellmanQ P_true_B r_B γ Q_true_B)
    (P_A : Matrix SA SA ℝ) (hP_A_tm : IsTransitionMatrix P_A)
    (hP_A_opt : agentTVDistA P_AB P_A = entanglementA P_AB)
    (P_B : Matrix SB SB ℝ) (hP_B_tm : IsTransitionMatrix P_B)
    (hP_B_opt : agentTVDistB P_AB P_B = entanglementB P_AB) :
    tvDist P_true_A P_A ≤ entanglementA P_AB ∧
    tvDist P_true_B P_B ≤ entanglementB P_AB ∧
    (⨆ p : SA × SB, |Q_AB p - (Q_true_A p.1 + Q_true_B p.2)|) ≤
      4 * γ * (entanglementA P_AB * rAmax + entanglementB P_AB * rBmax) / (1 - γ) ^ 2 := by
  sorry
