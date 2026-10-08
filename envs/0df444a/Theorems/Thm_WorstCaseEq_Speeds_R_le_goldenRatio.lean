-- Prove2me | Theorems.Thm_WorstCaseEq_Speeds_R_le_goldenRatio
-- name    : WorstCaseEq.Speeds.R_le_goldenRatio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:12:47.379073+00:00
-- url     : https://prove2.me/theorems/9833fecc-e74d-4f10-a255-397b15ec598a
-- title:
--   Theorem 4, second sentence, PDF p. 6 — on s₁ ≤ s₂ ≤ φs₁, R = 1 + s₂/(s₁ + s₂) ≤ φ, with equality at s₂/s₁ = φ
-- statement:
--   Let $\varphi=(1+\sqrt5)/2$ be the golden ratio and let $0<s_1\le s_2\le\varphi s_1$. Then
--   $$
--   R=1+\frac{s_2}{s_1+s_2}\le\varphi,
--   $$
--   and $R=\varphi$ when $s_2/s_1=\varphi$.
--
--   So the lower bound of Theorem 4 is largest, equal to the golden ratio, at the edge $s_2=\varphi s_1$ of the range on which it applies.
--
--   **Formalization Note** The ratio condition $s_2/s_1=\varphi$ is written $s_2=\varphi s_1$, equivalent because $s_1>0$. The golden ratio is Mathlib's `Real.goldenRatio`.
-- source:
--   Koutsoupias & Papadimitriou, Worst-case equilibria (journal version, 2009), PDF p. 6, Theorem 4 (second sentence)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model

namespace WorstCaseEq.Speeds

theorem R_le_goldenRatio (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₁₂ : s₁ ≤ s₂)
    (hφ : s₂ ≤ Real.goldenRatio * s₁) :
    1 + s₂ / (s₁ + s₂) ≤ Real.goldenRatio ∧
      (s₂ = Real.goldenRatio * s₁ → 1 + s₂ / (s₁ + s₂) = Real.goldenRatio) := by sorry

end WorstCaseEq.Speeds
