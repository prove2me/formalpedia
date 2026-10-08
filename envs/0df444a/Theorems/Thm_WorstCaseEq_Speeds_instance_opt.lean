-- Prove2me | Theorems.Thm_WorstCaseEq_Speeds_instance_opt
-- name    : WorstCaseEq.Speeds.instance_opt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:54.693484+00:00
-- url     : https://prove2.me/theorems/4b6b1ae2-6f54-4325-b78f-cf47f919c231
-- title:
--   Proof of Theorem 4, PDF p. 6 — with w₁ = s₂, w₂ = s₁ on speeds s₁, s₂ > 0, opt = 1
-- statement:
--   Let $s_1,s_2>0$ be the speeds of two links and consider two agents with traffic $w_1=s_2$ and $w_2=s_1$. The least makespan over all pure assignments of the two agents to the two links is
--   $$
--   \operatorname{opt}=1,
--   $$
--   attained by placing agent 1 on link 2 and agent 2 on link 1.
--
--   This is the denominator of the ratio in Theorem 4.
--
--   **Formalization Note** The paper's proof has $s_1\le s_2$ in force; the value $\operatorname{opt}=1$ holds for all positive speeds, so only positivity is assumed.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 6, proof of Theorem 4 ("and opt = 1")

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem instance_opt (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    opt (instWeights s₁ s₂) (speeds s₁ s₂) = 1 := by sorry

end WorstCaseEq.Speeds
