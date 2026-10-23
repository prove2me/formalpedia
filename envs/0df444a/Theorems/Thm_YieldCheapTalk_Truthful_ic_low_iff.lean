-- Prove2me | Theorems.Thm_YieldCheapTalk_Truthful_ic_low_iff
-- name    : YieldCheapTalk.Truthful.ic_low_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:49.389997+00:00
-- url     : https://prove2.me/theorems/3055638b-6535-49e2-b84b-fcb040cd7ddf
-- title:
--   Proof of Proposition 2, OA p. 4 — (B.5) ⇔ [1 + η(1/θ_H + 1/θ_L − 1)]w ≤ Σ µ(m|L)a_m
-- statement:
--   Assume the standing assumptions of the model. Then the low type's incentive condition
--   $$[Q^r(\theta_L, a_H) - Q^r(\theta_H, a_H)]\mu(H\mid L) \ge [Q^r(\theta_H, a_L) - Q^r(\theta_L, a_L)]\mu(L\mid L) \tag{B.5}$$
--   holds if and only if
--   $$\Big[1 + \eta\Big(\frac{1}{\theta_H} + \frac{1}{\theta_L} - 1\Big)\Big] w \le \sum_{m\in M}\mu(m\mid L)\,a_m ,$$
--   the right inequality of (6).
--
--   Together with the high-type counterpart, this identifies the IC condition (5) with condition (6) of Proposition 2.
-- source:
--   Lu, Can a Supplier’s Yield Risk Be Truthfully Communicated via Cheap Talk?, author manuscript of 14 July 2024 (MSOM, doi:10.1287/msom.2023.0089), OA p. 4 (PDF 31), Online Appendix B, proof of Proposition 2, (B.5)

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem ic_low_iff (M : Model) (hM : M.Standing) :
    (M.Qr (M.theta .L) (M.a .H) - M.Qr (M.theta .H) (M.a .H)) * M.mu .H .L ≥
          (M.Qr (M.theta .H) (M.a .L) - M.Qr (M.theta .L) (M.a .L)) * M.mu .L .L ↔
      (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w ≤
        ∑ m, M.mu m .L * M.a m := by sorry
end YieldCheapTalk.Truthful
