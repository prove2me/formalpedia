-- Prove2me | Theorems.Thm_WorstCaseEq_Speeds_instance_isNash
-- name    : WorstCaseEq.Speeds.instance_isNash
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:52.888002+00:00
-- url     : https://prove2.me/theorems/fc694767-aeb1-4163-a185-ab427815f947
-- title:
--   Proof of Theorem 4, PDF p. 6 — with w₁ = s₂, w₂ = s₁ on speeds s₁ ≤ s₂ ≤ φs₁, the stated mixed profile is a Nash equilibrium
-- statement:
--   Let $0<s_1\le s_2\le\varphi s_1$, where $\varphi=(1+\sqrt5)/2$. Consider two links with speeds $s_1,s_2$ and two agents with traffic $w_1=s_2$ and $w_2=s_1$, with no other traffic on the links. Let agent $i$ choose link 1 with probability $p_i^1$ and link 2 with probability $p_i^2=1-p_i^1$, where
--   $$
--   p_1^1=\frac{s_1^2}{s_2(s_1+s_2)},\qquad p_2^1=1-\frac{s_2^2}{s_1(s_1+s_2)} .
--   $$
--   Then this mixed profile is a Nash equilibrium: both $p_1$ and $p_2$ are probability distributions, and neither agent can lower its expected delay by changing its strategy unilaterally.
--
--   This is the equilibrium whose social cost gives the lower bound of Theorem 4.
--
--   **Formalization Note** The paper's agents 1, 2 and links 1, 2 are `0, 1`; the weight vector is `![s₂, s₁]` and the speed vector `![s₁, s₂]`. The speeds enter only through the hypotheses; $s_2>0$ follows from $0<s_1\le s_2$.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 6, proof of Theorem 4

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem instance_isNash (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ Real.goldenRatio * s₁) :
    IsNash (instWeights s₁ s₂) (speeds s₁ s₂) (instProfile s₁ s₂) := by sorry

end WorstCaseEq.Speeds
