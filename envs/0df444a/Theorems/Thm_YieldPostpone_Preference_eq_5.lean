-- Prove2me | Theorems.Thm_YieldPostpone_Preference_eq_5
-- name    : YieldPostpone.Preference.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:30.739976+00:00
-- url     : https://prove2.me/theorems/73da6289-261a-4575-bec1-0e71ff08a206
-- title:
--   (5), App. B, PDF p. 34 — the responsive retail price is (a − q̂)/b below a/2 and a/(2b) above
-- statement:
--   Let $a,b>0$ and let $x>0$ units be available for sale. Over admissible retail prices $0<p<a/b$, the revenue $p\min\{a-bp,\,x\}$ has a unique maximizer, namely
--   $$p^*(x)=\begin{cases}\dfrac{a-x}{b}, & 0<x<\dfrac a2,\\[2mm] \dfrac{a}{2b}, & x\ge\dfrac a2.\end{cases}$$
--
--   This is the retailer's ex post pricing rule under responsive pricing (scenarios OR and DR): with little stock the retailer prices to clear it, with ample stock it charges the monopoly price and leaves units unsold.
--
--   **Formalization Note** The page writes the rule with indicators of $0<\hat q<a/2$ and $\hat q>a/2$; at $x=a/2$ the two expressions coincide, so the boundary is assigned to the second case here. The statement asserts that the set of maximizers is exactly $\{p^*(x)\}$.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), App. B, PDF p. 34 (appendix p. 2), (5)

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- (5), App. B, PDF p. 34: with `x > 0` units available, the revenue `p min{a − bp, x}` over
admissible prices `0 < p < a/b` has the unique maximizer `p*(x) = (a − x)/b` if `x < a/2`
and `p*(x) = a/(2b)` if `x ≥ a/2`. -/
theorem eq_5 (P : Params) (hP : P.Valid) (x : ℝ) (hx : 0 < x) :
    {p : ℝ | pAdm P p ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x} =
      {if x < P.a / 2 then (P.a - x) / P.b else P.a / (2 * P.b)} := by sorry

end YieldPostpone.Preference
