-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_eq_4
-- name    : YieldPostpone.Interplay.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:24.47103+00:00
-- url     : https://prove2.me/theorems/3eb8827d-34f9-4c7f-9c7e-a4741a326cfc
-- title:
--   (4), App. B, PDF p. 33 — under pay-by-delivery the supplier produces exactly q below c/(α(1−θ)), anything in [q, q/α] at it, and exactly q/α above it
-- statement:
--   Consider a pay-by-delivery scenario (DA or DR) with parameters $a,b>0$, $0<\alpha,\theta<1$, $\mu=\alpha(1-\theta)+\theta$ and cost $0<c<a\mu/b$. Fix a wholesale price $w$ with $c/\mu<w<a/b$ and an order $q>0$. The supplier's expected profit from producing $Q\ge0$ is
--   $$\pi_S(Q)=-cQ+\theta w\min\{Q,q\}+(1-\theta)w\min\{\alpha Q,q\}.$$
--   Let $w_0=c/(\alpha(1-\theta))$.
--
--   1. If $w<w_0$, then $Q=q$ is the unique maximizer of $\pi_S$ over $Q\ge0$, and the delivered quantity is $\hat q=Yq$ (that is, $q$ when $Y=1$ and $\alpha q$ when $Y=\alpha$).
--   2. If $w=w_0$, the maximizers of $\pi_S$ over $Q\ge0$ are exactly the $Q$ with $q\le Q\le q/\alpha$; in particular the page's choice $Q=q/\alpha$ is optimal.
--   3. If $w>w_0$, then $Q=q/\alpha$ is the unique maximizer, and the delivered quantity is $\hat q=q$ in both yield states.
--
--   This is the supplier's production response used in every pay-by-delivery equilibrium: below $w_0$ it never inflates production, above $w_0$ it inflates to secure full delivery.
--
--   **Formalization Note** The page assigns the tie $w=w_0$ to inflation. At $w=w_0$ every $Q\in[q,q/\alpha]$ is optimal, so the tie is a selection, not a property of the maximizers: the statement gives the whole set of maximizers at $w=w_0$ (which contains the page's $Q=q/\alpha$), and the mission's equilibrium predicate selects $Q=q$ there (see the Setting). The order $q>0$ is assumed; at $q=0$ the only maximizer is $Q=0$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. B, PDF p. 33 (appendix p. 1), display (4)

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem eq_4 (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (hcμ : c < P.a * μ P / P.b)
    (k : Scenario) (hk : k.byDelivery = true) (w q : ℝ) (hw : wAdm P c k w) (hq : 0 < q) :
    (w < c / (P.α * (1 - P.θ)) →
      (∀ Q : ℝ, 0 ≤ Q →
        ((∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q) ↔ Q = q)) ∧
      delivered 1 q q = q ∧ delivered P.α q q = P.α * q) ∧
    (w = c / (P.α * (1 - P.θ)) →
      ∀ Q : ℝ, 0 ≤ Q →
        ((∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q) ↔
          (q ≤ Q ∧ Q ≤ q / P.α))) ∧
    (c / (P.α * (1 - P.θ)) < w →
      (∀ Q : ℝ, 0 ≤ Q →
        ((∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q) ↔
          Q = q / P.α)) ∧
      delivered 1 (q / P.α) q = q ∧ delivered P.α (q / P.α) q = q) := by sorry

end YieldPostpone.Interplay
