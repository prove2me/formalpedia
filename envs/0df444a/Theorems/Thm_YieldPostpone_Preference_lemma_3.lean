-- Prove2me | Theorems.Thm_YieldPostpone_Preference_lemma_3
-- name    : YieldPostpone.Preference.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:23.471979+00:00
-- url     : https://prove2.me/theorems/c9e1ab31-956e-4a71-988b-89a80115dfa6
-- title:
--   Lemma 3, p. 12, with App. B.3, PDF p. 36 — the DA equilibrium: existence and the outcome on each open piece split at c^DA
-- statement:
--   Consider scenario DA (pay-by-delivery, ex ante pricing) with parameters $a,b>0$, $\alpha,\theta\in(0,1)$, $\mu=\alpha(1-\theta)+\theta$, and
--   $$c^{DA}=\frac{a\alpha(\mu-\theta\sqrt\mu)}{b(\alpha+\theta)}.$$
--   Then:
--
--   1. for every cost $0<c<a\mu/b$ a subgame-perfect equilibrium exists;
--   2. if $0<c<c^{DA}$, every equilibrium has
--   $$\big(\pi^{DA}_R,\pi^{DA}_S,CS^{DA}\big)=\Big(\tfrac{(bc-a\alpha)^2}{16b\alpha^2},\ \tfrac{(bc-a\alpha)^2}{8b\alpha^2},\ \tfrac{(bc-a\alpha)^2}{32b\alpha^2}\Big);$$
--   3. if $c^{DA}<c<a\mu/b$, every equilibrium has
--   $$\big(\pi^{DA}_R,\pi^{DA}_S,CS^{DA}\big)=\Big(\tfrac{(bc-a\mu)^2}{16b\mu},\ \tfrac{(bc-a\mu)^2}{8b\mu},\ \tfrac{(bc-a\mu)^2(\alpha(2-\alpha)(1-\theta)+\theta)}{32b\mu^2}\Big).$$
--
--   This is the equilibrium of the payment-postponement scenario; Proposition 2 compares its retailer profit with those of OR and DR.
--
--   **Formalization Note** Equilibrium means the subgame-perfect equilibrium of the mission's setting. The page states the pieces on $0\le c<c^{DA}$ and $c^{DA}\le c<a\mu/b$; uniqueness is stated on the open pieces only, since at the threshold the supplier is indifferent between two wholesale prices. The lemma's last sentence (who inflates) is not posed. No assumption on $\alpha$ beyond $0<\alpha<1$ is made.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), p. 12, Lemma 3; App. B.3, PDF p. 36 (appendix p. 4), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- Lemma 3, p. 12, with the B.3 summary, PDF p. 36: scenario DA (pay-by-delivery, ex ante
pricing). For every cost `0 < c < aμ/b` a subgame-perfect equilibrium exists, and every
equilibrium has the outcome `(π_R, π_S, CS)` of B.3 on each open piece `0 < c < c^DA` and
`c^DA < c < aμ/b`. -/
theorem lemma_3 (P : Params) (hP : P.Valid) :
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b → ∃ σ : Profile, IsSPE P c .DA σ) ∧
    (∀ (c : ℝ) (σ : Profile), 0 < c → c < cDA P → IsSPE P c .DA σ →
      piR P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) ∧
      piS P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) ∧
      CS P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
    (∀ (c : ℝ) (σ : Profile), cDA P < c → c < P.a * μ P / P.b → IsSPE P c .DA σ →
      piR P c .DA σ = (P.b * c - P.a * μ P) ^ 2 / (16 * P.b * μ P) ∧
      piS P c .DA σ = (P.b * c - P.a * μ P) ^ 2 / (8 * P.b * μ P) ∧
      CS P c .DA σ = (P.b * c - P.a * μ P) ^ 2 * (P.α * (2 - P.α) * (1 - P.θ) + P.θ)
          / (32 * P.b * μ P ^ 2)) := by sorry

end YieldPostpone.Preference
