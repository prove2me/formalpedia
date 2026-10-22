-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_eq_5
-- name    : YieldPostpone.Interplay.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:27.431254+00:00
-- url     : https://prove2.me/theorems/d304f87e-1fa3-4e76-8562-b24a5f4ff135
-- title:
--   (5), App. B, PDF p. 34 — the ex post price p*(q̂) = (a − q̂)/b for q̂ < a/2 and a/(2b) for q̂ ≥ a/2
-- statement:
--   Let $a,b>0$ and let $x\ge 0$ be the quantity available for sale. Under responsive pricing the retailer chooses $p\in(0,a/b)$ to maximize its revenue $p\min\{a-bp,x\}$. The maximizer is unique and equals
--   $$p^*(x)=\begin{cases}\dfrac{a-x}{b}, & 0<x<\dfrac a2,\\[2mm] \dfrac{a}{2b}, & x\ge \dfrac a2.\end{cases}$$
--
--   When stock is scarce the retailer clears it at the market-clearing price; when stock is ample it charges the monopoly price and leaves the excess unsold.
--
--   **Formalization Note** The page writes the second case as $x>a/2$; at $x=a/2$ both formulas give $a/(2b)$, which is included. The statement asserts that $p^*(x)$ is the unique maximizer over the admissible prices $0<p<a/b$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. B, PDF p. 34 (appendix p. 2), display (5)

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem eq_5 (P : Params) (hP : P.Valid) (x : ℝ) :
    (0 < x → x < P.a / 2 →
      ∀ p : ℝ, pAdm P p →
        ((∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x) ↔ p = (P.a - x) / P.b)) ∧
    (P.a / 2 ≤ x →
      ∀ p : ℝ, pAdm P p →
        ((∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x) ↔ p = P.a / (2 * P.b))) := by sorry

end YieldPostpone.Interplay
