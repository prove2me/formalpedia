-- Prove2me | Theorems.Thm_markov_entanglement_local_tv_bounds
-- name    : markov_entanglement_local_tv_bounds
-- status  : Proved
-- author  : @allychan327
-- created : 2026-07-18T15:10:17.068194+00:00
-- url     : https://prove2.me/theorems/d441b4c4-6826-4cce-aeaf-8603782c3af3
-- title:
--   Marginalized local transitions inherit agent-wise TV bounds
-- statement:
--   For a finite two-agent transition system and a strictly positive occupancy distribution, each marginalized local transition is no farther in ordinary row-wise total variation from a candidate local transition than the joint transition is in the corresponding agent-wise total variation distance. In particular, when the candidate attains the Markov-entanglement infimum, the local TV distances are bounded by the agent-A and agent-B entanglement measures.
-- source:
--   Chen and Peng, “Multi-agent Markov Entanglement,” arXiv:2506.02385v3, Theorem 4 (p. 16) and Appendix F first argument (pp. 36–37), especially the arbitrary-subset marginalization calculation concluding the two local TV bounds. https://arxiv.org/pdf/2506.02385v3

import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

/-- Chen--Peng, Appendix F, pp. 36--37: marginalized local transitions are within
the corresponding agent-wise distance of any candidate local transition. -/
theorem markov_entanglement_local_tv_bounds
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P_AB : Matrix (SA × SB) (SA × SB) ℝ) (hP_AB : IsTransitionMatrix P_AB)
    (μ : SA × SB → ℝ) (hμ : IsPositiveDist μ)
    (P_true_A : Matrix SA SA ℝ) (hP_true_A_tm : IsTransitionMatrix P_true_A)
    (hP_true_A : IsLocalTransitionA P_AB μ P_true_A)
    (P_true_B : Matrix SB SB ℝ) (hP_true_B_tm : IsTransitionMatrix P_true_B)
    (hP_true_B : IsLocalTransitionB P_AB μ P_true_B)
    (P_A : Matrix SA SA ℝ) (hP_A_tm : IsTransitionMatrix P_A)
    (hP_A_opt : agentTVDistA P_AB P_A = entanglementA P_AB)
    (P_B : Matrix SB SB ℝ) (hP_B_tm : IsTransitionMatrix P_B)
    (hP_B_opt : agentTVDistB P_AB P_B = entanglementB P_AB) :
    tvDist P_true_A P_A ≤ entanglementA P_AB ∧
    tvDist P_true_B P_B ≤ entanglementB P_AB := by
  sorry
