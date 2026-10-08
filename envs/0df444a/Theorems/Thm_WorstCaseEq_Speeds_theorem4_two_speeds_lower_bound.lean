-- Prove2me | Theorems.Thm_WorstCaseEq_Speeds_theorem4_two_speeds_lower_bound
-- name    : WorstCaseEq.Speeds.theorem4_two_speeds_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:12:08.39642+00:00
-- url     : https://prove2.me/theorems/3f1ac494-f6e2-42e8-a26e-20432f86b9a3
-- title:
--   Theorem 4, PDF p. 6 — the price of anarchy for two links with speeds s₁ ≤ s₂ ≤ φs₁ is at least R = 1 + s₂/(s₁ + s₂), and R ≤ φ with equality at s₂/s₁ = φ
-- statement:
--   Consider load balancing on two parallel links with speeds $s_1\le s_2$: each agent sends its traffic over one link, an agent on link $j$ carrying total traffic $L$ experiences delay $L/s_j$, the social cost of a mixed profile is the expected maximum over the links of load divided by speed, and $\operatorname{opt}$ is the least such maximum over pure assignments. Let $\varphi=(1+\sqrt5)/2$ and suppose
--   $$
--   0<s_1\le s_2\le\varphi\,s_1 .
--   $$
--   Then:
--
--   1. **(Lower bound.)** The price of anarchy is at least $R=1+s_2/(s_1+s_2)$: there are finitely many agents with positive traffic and a Nash equilibrium $p$ of this game with $\operatorname{opt}>0$ and
--   $$
--   \operatorname{cost}(p)=\Big(1+\frac{s_2}{s_1+s_2}\Big)\operatorname{opt}.
--   $$
--   2. **(Maximum value.)** $R\le\varphi$ on this range.
--   3. **(Attained.)** If $s_2/s_1=\varphi$ then $R=\varphi$.
--
--   With identical links ($s_1=s_2$) the bound is $3/2$, the lower bound of Theorem 1 for two links; the theorem shows that unequal speeds push the worst-case ratio up to the golden ratio.
--
--   **Formalization Note** "The price of anarchy is at least $R$" is stated as the existence of an instance and an equilibrium whose social cost equals $R$ times a positive optimum, rather than through a supremum or a quotient (a quotient would take the junk value $0$ when $\operatorname{opt}=0$). The speed vector is `![s₁, s₂]` (the paper's links 1, 2 are `0, 1`). The ratio conditions are written $s_2\le\varphi s_1$ and $s_2=\varphi s_1$, equivalent because $s_1>0$. Positive traffic $w_i>0$ is part of the model and is required of the witness. The social cost with speeds is not printed in the paper; the definition used (expected maximum of load divided by speed) is the one its cost computation uses.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 6, Theorem 4

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem theorem4_two_speeds_lower_bound (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ Real.goldenRatio * s₁) :
    (∃ (n : ℕ) (w : Fin n → ℝ) (p : Fin n → Fin 2 → ℝ),
        (∀ i, 0 < w i) ∧ IsNash w ![s₁, s₂] p ∧ 0 < opt w ![s₁, s₂] ∧
          socialCost w ![s₁, s₂] p = (1 + s₂ / (s₁ + s₂)) * opt w ![s₁, s₂]) ∧
      1 + s₂ / (s₁ + s₂) ≤ Real.goldenRatio ∧
      (s₂ = Real.goldenRatio * s₁ → 1 + s₂ / (s₁ + s₂) = Real.goldenRatio) := by sorry

end WorstCaseEq.Speeds
