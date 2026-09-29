-- Prove2me | Theorems.Thm_markov_entanglement_bellman_q_error_of_local_tv
-- name    : markov_entanglement_bellman_q_error_of_local_tv
-- status  : Proved
-- author  : @allychan327
-- created : 2026-07-18T15:10:38.561291+00:00
-- url     : https://prove2.me/theorems/b58ff354-d3fb-4ca8-8963-9d4a1c62853d
-- title:
--   Bellman Q-decomposition error from local TV control
-- statement:
--   For finite two-agent transition matrices with discount factor $0\le\gamma<1$ and bounded additive local rewards, assume candidate local transitions attain the agent-wise Markov-entanglement distances and that the true marginalized local transitions satisfy the corresponding ordinary total-variation bounds. Then the sup-norm error between the joint Bellman Q-value and the sum of the two local Bellman Q-values is at most $$\frac{4\gamma}{(1-\gamma)^2}\bigl(E_A(P_{AB})r_{A,\max}+E_B(P_{AB})r_{B,\max}\bigr).$$
-- source:
--   Chen and Peng, “Multi-agent Markov Entanglement,” arXiv:2506.02385v3, Theorem 4 (p. 16), proof sketch §5.3 (p. 17, Eq. (6)), and Appendix F Bellman resolvent perturbation argument (pp. 37–38). https://arxiv.org/pdf/2506.02385v3

import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

/-- Chen--Peng, Appendix F, pp. 37--38: the Bellman resolvent perturbation bound,
assuming the local-TV consequences established in the first part of the proof. -/
theorem markov_entanglement_bellman_q_error_of_local_tv
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P_AB : Matrix (SA × SB) (SA × SB) ℝ) (hP_AB : IsTransitionMatrix P_AB)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r_A : SA → ℝ) (r_B : SB → ℝ) (rAmax rBmax : ℝ)
    (hrAmax : 0 ≤ rAmax) (hrBmax : 0 ≤ rBmax)
    (hrA : ∀ a, |r_A a| ≤ rAmax) (hrB : ∀ b, |r_B b| ≤ rBmax)
    (P_true_A : Matrix SA SA ℝ) (hP_true_A_tm : IsTransitionMatrix P_true_A)
    (P_true_B : Matrix SB SB ℝ) (hP_true_B_tm : IsTransitionMatrix P_true_B)
    (Q_AB : SA × SB → ℝ) (hQ_AB : IsBellmanQ P_AB (fun p => r_A p.1 + r_B p.2) γ Q_AB)
    (Q_true_A : SA → ℝ) (hQ_true_A : IsBellmanQ P_true_A r_A γ Q_true_A)
    (Q_true_B : SB → ℝ) (hQ_true_B : IsBellmanQ P_true_B r_B γ Q_true_B)
    (P_A : Matrix SA SA ℝ) (hP_A_tm : IsTransitionMatrix P_A)
    (hP_A_opt : agentTVDistA P_AB P_A = entanglementA P_AB)
    (P_B : Matrix SB SB ℝ) (hP_B_tm : IsTransitionMatrix P_B)
    (hP_B_opt : agentTVDistB P_AB P_B = entanglementB P_AB)
    (hTVA : tvDist P_true_A P_A ≤ entanglementA P_AB)
    (hTVB : tvDist P_true_B P_B ≤ entanglementB P_AB) :
    (⨆ p : SA × SB, |Q_AB p - (Q_true_A p.1 + Q_true_B p.2)|) ≤
      4 * γ * (entanglementA P_AB * rAmax + entanglementB P_AB * rBmax) / (1 - γ) ^ 2 := by
  sorry
