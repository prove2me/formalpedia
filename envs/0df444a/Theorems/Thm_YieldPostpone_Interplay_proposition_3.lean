-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_proposition_3
-- name    : YieldPostpone.Interplay.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:24.519751+00:00
-- url     : https://prove2.me/theorems/9db14152-efd8-4af1-b710-76b376557127
-- title:
--   Proposition 3, p. 18 — for α ≥ 9/16 on H₃ the two postponements are substitutes, then complements on (c^DR_1, Ĉ), then substitutes, then neutral
-- statement:
--   **Proposition 3.** Let $a,b>0$, $0<\alpha,\theta<1$ with $\alpha\ge9/16$ and $(\alpha,\theta)\in\mathcal H_3$, that is $\theta_2(\alpha)<\theta<1$, and let $\mu=\alpha(1-\theta)+\theta$. Then:
--
--   1. for every cost $0<c<a\mu/b$, each of the four games OA, OR, DA, DR has a subgame-perfect equilibrium;
--   2. there exists $\hat C$ with $0<\hat C<a\mu/b$ such that, for every cost $0<c<a\mu/b$ and every choice of subgame-perfect equilibria of the four scenarios at that cost, the interaction
--   $$V=\big(\pi^{DR}_R-\pi^{OR}_R\big)-\big(\pi^{DA}_R-\pi^{OA}_R\big)$$
--   of Definition 1 satisfies
--      - (i) $V<0$ if $0<c<c^{DR}_1$ or $\hat C<c<c^{DA}$;
--      - (ii) $V>0$ if $c^{DR}_1<c<\hat C$;
--      - (iii) $V=0$ if $c^{DA}<c<\frac ab\mu$.
--
--   When full yield is likely, postponing payment and postponing pricing are substitutes at low and moderately high cost, complements at intermediate cost, and do not interact at high cost, where payment postponement is irrelevant.
--
--   **Formalization Note** (1) $\hat C$ is existential, as printed: it depends on $(a,b,\alpha,\theta)$ only and is chosen before $c$. Formula (7) of the appendix is not used; at $(\alpha,\theta)=(0.6,0.75)$ it exceeds $c^{DA}$. (2) Part 1 is added so that part 2 is not vacuous: it states that each scenario's equilibrium set is nonempty. (3) The four profiles are equilibria of their own scenarios at the same parameters and cost. (4) The intervals are open, as printed.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 18, Proposition 3; Definition 1, p. 17; H₃, App. B.1, PDF p. 34

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting
import Definitions.Def_YieldPostpone_Interplay_Interaction

namespace YieldPostpone.Interplay

theorem proposition_3 (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (hH : H3 P.α P.θ) :
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧ (∃ σ : Profile, IsSPE P c .OR σ) ∧
      (∃ σ : Profile, IsSPE P c .DA σ) ∧ (∃ σ : Profile, IsSPE P c .DR σ)) ∧
    ∃ Chat : ℝ, 0 < Chat ∧ Chat < P.a * μ P / P.b ∧
      ∀ (c : ℝ) (σOA σOR σDA σDR : Profile), 0 < c → c < P.a * μ P / P.b →
        IsSPE P c .OA σOA → IsSPE P c .OR σOR → IsSPE P c .DA σDA → IsSPE P c .DR σDR →
        ((c < cDR1 P ∨ (Chat < c ∧ c < cDA P)) → interaction P c σOA σOR σDA σDR < 0) ∧
        (cDR1 P < c → c < Chat → 0 < interaction P c σOA σOR σDA σDR) ∧
        (cDA P < c → interaction P c σOA σOR σDA σDR = 0) := by sorry

end YieldPostpone.Interplay
