-- Prove2me | Theorems.Thm_YieldPostpone_Payment_responsive_price
-- name    : YieldPostpone.Payment.responsive_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:24.794993+00:00
-- url     : https://prove2.me/theorems/6198490a-80fa-402a-93f2-22338dca3763
-- title:
--   Appendix B (5) — price after delivery
-- statement:
--   For a positive delivered quantity $x$, an admissible price that maximizes sales revenue $p\min\{a-bp,x\}$ is
--
--   $$p^*(x)=\begin{cases}(a-x)/b,&0<x<a/2,\\a/(2b),&x\ge a/2.\end{cases}$$
--
--   This price is used after delivery in scenarios OR and DR. The page prints the second indicator as $\hat q>a/2$ and leaves $x=a/2$ uncovered; there the two displayed expressions coincide, so the Lean assigns it to the second branch.
--
--   **Formalization Note** The paper's indicators omit the equality case; the continuous value at the boundary is used.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. B, PDF p. 34 (appendix p. 2), (5)

import Definitions.Def_YieldPostpone_Payment_Setting

namespace YieldPostpone.Payment

theorem responsive_price (P : Params) (x : ℝ) (hP : P.Valid) (hx : 0 < x) :
    let p := if x < P.a / 2 then (P.a - x) / P.b else P.a / (2 * P.b)
    pAdm P p ∧ ∀ p', pAdm P p' → salesRev P p' x ≤ salesRev P p x := by sorry

end YieldPostpone.Payment
