-- Prove2me | Theorems.Thm_WorstCaseEq_Speeds_instance_probs_mem_Icc_iff
-- name    : WorstCaseEq.Speeds.instance_probs_mem_Icc_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:58.674479+00:00
-- url     : https://prove2.me/theorems/d8878ac1-4cf2-4e2f-96e6-8e49228c30cf
-- title:
--   Proof of Theorem 4, PDF p. 6 — for s₁ ≤ s₂ the instance's probabilities lie in [0, 1] iff s₂ ≤ φ s₁
-- statement:
--   Let $0<s_1\le s_2$ be the speeds of two links and let $\varphi=(1+\sqrt5)/2$ be the golden ratio. The two numbers
--   $$
--   p_1^1=\frac{s_1^2}{s_2(s_1+s_2)},\qquad p_2^1=1-\frac{s_2^2}{s_1(s_1+s_2)}
--   $$
--   both lie in the interval $[0,1]$ if and only if
--   $$
--   s_2\le\varphi\, s_1 .
--   $$
--
--   These are the probabilities of the equilibrium used in the proof of Theorem 4. The "if" direction is why Theorem 4 assumes $s_2\le\varphi s_1$; the "only if" direction is the closing remark of the proof that for $s_2/s_1>\varphi$ these probabilities fall outside $[0,1]$.
--
--   **Formalization Note** The ratio condition $s_2/s_1\le\varphi$ is written $s_2\le\varphi s_1$, which is equivalent because $s_1>0$. The golden ratio is Mathlib's `Real.goldenRatio`, defined as $(1+\sqrt5)/2$.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 6, proof of Theorem 4 (the probabilities p₁¹, p₂¹ and the closing remark on s₂/s₁ > φ)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem instance_probs_mem_Icc_iff (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂) :
    (s₁ ^ 2 / (s₂ * (s₁ + s₂)) ∈ Set.Icc (0 : ℝ) 1 ∧
        1 - s₂ ^ 2 / (s₁ * (s₁ + s₂)) ∈ Set.Icc (0 : ℝ) 1) ↔
      s₂ ≤ Real.goldenRatio * s₁ := by sorry

end WorstCaseEq.Speeds
