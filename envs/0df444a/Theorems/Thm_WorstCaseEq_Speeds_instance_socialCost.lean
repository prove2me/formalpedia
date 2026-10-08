-- Prove2me | Theorems.Thm_WorstCaseEq_Speeds_instance_socialCost
-- name    : WorstCaseEq.Speeds.instance_socialCost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:12:34.348035+00:00
-- url     : https://prove2.me/theorems/e241852e-e790-4ebd-8e5b-aba2b51fa5bc
-- title:
--   Proof of Theorem 4, PDF p. 6 — the instance's social cost is (s₁ + 2s₂)/(s₁ + s₂)
-- statement:
--   Let $0<s_1\le s_2$. On two links with speeds $s_1,s_2$, let two agents with traffic $w_1=s_2$, $w_2=s_1$ play the mixed profile
--   $$
--   p_1^1=\frac{s_1^2}{s_2(s_1+s_2)},\qquad p_2^1=1-\frac{s_2^2}{s_1(s_1+s_2)},\qquad p_i^2=1-p_i^1 .
--   $$
--   Then the expected makespan (the expected maximum over the two links of load divided by speed) is
--   $$
--   \operatorname{cost}=\Big(\frac{p_1^1p_2^1}{s_1}+\frac{p_1^2p_2^2}{s_2}\Big)(w_1+w_2)+\Big(\frac{p_1^1p_2^2}{s_1}+\frac{p_1^2p_2^1}{s_2}\Big)w_1=\frac{s_1+2s_2}{s_1+s_2}.
--   $$
--
--   Together with $\operatorname{opt}=1$ this gives the ratio $1+s_2/(s_1+s_2)$ of Theorem 4.
--
--   **Formalization Note** The identity is algebraic and does not need $s_2\le\varphi s_1$ (outside that range the "profile" is not a probability distribution, but the expected-makespan sum is still defined). The hypothesis $s_1\le s_2$ decides which link carries the maximum when the agents split ($w_1/s_1=s_2/s_1\ge s_1/s_2=w_2/s_2$).
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 6, proof of Theorem 4 (cost computation)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem instance_socialCost (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) :
    socialCost (instWeights s₁ s₂) (speeds s₁ s₂) (instProfile s₁ s₂)
      = (s₁ + 2 * s₂) / (s₁ + s₂) := by sorry

end WorstCaseEq.Speeds
