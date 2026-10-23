-- Prove2me | Theorems.Thm_YieldPostpone_Preference_lemma_3_at_cDA
-- name    : YieldPostpone.Preference.lemma_3_at_cDA
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T05:30:41.84868+00:00
-- url     : https://prove2.me/theorems/e74d6e88-c7f1-49e0-b463-01e37c6013d1
-- title:
--   Lemma 3, p. 12 — at the threshold $c=c^{DA}$ every DA equilibrium yields the second-piece profits $\pi_R,\pi_S$
-- statement:
--   Let $a,b>0$, $\alpha,\theta\in(0,1)$, $\mu=\alpha(1-\theta)+\theta$, and let the production cost sit exactly at the DA threshold
--   $$c=c^{DA}=\frac{a\alpha(\mu-\theta\sqrt\mu)}{b(\alpha+\theta)}.$$
--   Then every subgame-perfect equilibrium of scenario DA (pay-by-delivery, ex ante pricing) gives the retailer and the supplier the profits of the second piece of Appendix B.3:
--   $$\pi^{DA}_R=\frac{(bc-a\mu)^2}{16b\mu},\qquad \pi^{DA}_S=\frac{(bc-a\mu)^2}{8b\mu}.$$
--
--   Lemma 3 states the pieces as $0\le c<c^{DA}$ and $c^{DA}\le c<(a/b)\mu$, so the threshold belongs to the second piece. The open-interval milestone `lemma_3` leaves this point out. At $c=c^{DA}$ the supplier is indifferent between the two candidate wholesale prices, and the two candidate outcomes give the retailer (and the supplier) the same profit, because $(bc-a\alpha)^2/\alpha^2=(bc-a\mu)^2/\mu$ exactly at $c^{DA}$. The consumer surplus is **not** asserted: it can differ between the two equilibria at the threshold.
--
--   This boundary value is needed to compare retailer profits across the whole range $c^{DR}_2<c<a\mu/b$ in Proposition 2, since $c^{DA}$ lies inside that range.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), p. 12, Lemma 3 (pieces 0 ≤ c < c^DA and c^DA ≤ c < (a/b)μ); App. B.3, PDF p. 36

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- Lemma 3, p. 12, at the threshold `c = c^DA` (the second piece is stated on
`c^DA ≤ c < (a/b)μ`): every DA equilibrium gives the retailer and the supplier the
second-piece profits of B.3. -/
theorem lemma_3_at_cDA (P : Params) (hP : P.Valid) :
    ∀ σ : Profile, IsSPE P (cDA P) .DA σ →
      piR P (cDA P) .DA σ = (P.b * cDA P - P.a * μ P) ^ 2 / (16 * P.b * μ P) ∧
      piS P (cDA P) .DA σ = (P.b * cDA P - P.a * μ P) ^ 2 / (8 * P.b * μ P) := by sorry

end YieldPostpone.Preference
