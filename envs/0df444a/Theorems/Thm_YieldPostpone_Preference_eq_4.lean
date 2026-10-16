-- Prove2me | Theorems.Thm_YieldPostpone_Preference_eq_4
-- name    : YieldPostpone.Preference.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:26.719982+00:00
-- url     : https://prove2.me/theorems/9aaa8191-95a2-4971-aefb-165cd1c01401
-- title:
--   (4), App. B, PDF p. 33 — under pay-by-delivery the supplier produces q if w < c/(α(1−θ)) and inflates to q/α if w > c/(α(1−θ))
-- statement:
--   Consider a pay-by-delivery scenario (DA or DR) with standing ranges $0<c<a\mu/b$, and a wholesale price $w$ with $c/\mu<w<a/b$. Given an order $q>0$, the supplier chooses its planned production $Q\ge0$ to maximize
--   $$\pi_S(Q)=-cQ+\theta w\min\{Q,q\}+(1-\theta)w\min\{\alpha Q,q\}.$$
--   Let $w_0=c/(\alpha(1-\theta))$. Then:
--
--   1. if $w<w_0$, the unique maximizer is $Q^*=q$, and the delivered quantity is $\hat q=Yq$ (that is, $q$ when $Y=1$ and $\alpha q$ when $Y=\alpha$);
--   2. if $w>w_0$, the unique maximizer is $Q^*=q/\alpha$ (production inflation), and the delivered quantity is $\hat q=q$ in both yield states.
--
--   This is the supplier's production best response, the last stage of backward induction under pay-by-delivery; it determines what the retailer anticipates when it orders.
--
--   **Formalization Note** The page assigns the boundary case $w=w_0$, where every $Q\in[q,q/\alpha]$ is optimal, to inflation; this statement leaves $w=w_0$ out, and the mission's equilibrium notion resolves that tie by $Q=q$ (see the setting). The standing range $0<c<a\mu/b$ of (3) is a hypothesis.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), App. B, PDF p. 33 (appendix p. 1), (4)

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- (4), App. B, PDF p. 33: under pay-by-delivery, for `c/μ < w < a/b` and an order `q > 0`,
the supplier's profit `−cQ + θ w min{Q, q} + (1 − θ) w min{αQ, q}` over `Q ≥ 0` is maximized
exactly at `Q = q` (delivery `Y q`) when `w < c/(α(1 − θ))`, and exactly at `Q = q/α`
(delivery `q`) when `w > c/(α(1 − θ))`. -/
theorem eq_4 (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (hcμ : c < P.a * μ P / P.b)
    (k : Scenario) (hk : k.byDelivery = true) (w q : ℝ) (hw₁ : c / μ P < w)
    (hw₂ : w < P.a / P.b) (hq : 0 < q) :
    (w < c / (P.α * (1 - P.θ)) →
      {Q : ℝ | 0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q} = {q} ∧
      delivered 1 q q = q ∧ delivered P.α q q = P.α * q) ∧
    (c / (P.α * (1 - P.θ)) < w →
      {Q : ℝ | 0 ≤ Q ∧ ∀ Q' : ℝ, 0 ≤ Q' →
          supplierProfit P c k w Q' q ≤ supplierProfit P c k w Q q} = {q / P.α} ∧
      delivered 1 (q / P.α) q = q ∧ delivered P.α (q / P.α) q = q) := by sorry

end YieldPostpone.Preference
