-- Prove2me | Theorems.Thm_YieldCheapTalk_Truthful_ic_high_iff
-- name    : YieldCheapTalk.Truthful.ic_high_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:43.31423+00:00
-- url     : https://prove2.me/theorems/63e54781-ab98-4dea-9b6e-aea22ee7c10c
-- title:
--   Proof of Proposition 2, OA pp. 3–4 — (5) is (B.4) ∧ (B.5), and (B.4) ⇔ Σ µ(m|H)a_m ≤ [1 + η(1/θ_H + 1/θ_L − 1)]w
-- statement:
--   Assume the standing assumptions of the model. Then:
--
--   1. The IC condition (5) holds if and only if both
--   $$[Q^r(\theta_H, a_H) - Q^r(\theta_L, a_H)]\mu(H\mid H) \ge [Q^r(\theta_L, a_L) - Q^r(\theta_H, a_L)]\mu(L\mid H) \tag{B.4}$$
--   and
--   $$[Q^r(\theta_L, a_H) - Q^r(\theta_H, a_H)]\mu(H\mid L) \ge [Q^r(\theta_H, a_L) - Q^r(\theta_L, a_L)]\mu(L\mid L) \tag{B.5}$$
--   hold.
--   2. (B.4) holds if and only if
--   $$\sum_{m\in M}\mu(m\mid H)\,a_m \le \Big[1 + \eta\Big(\frac{1}{\theta_H} + \frac{1}{\theta_L} - 1\Big)\Big] w ,$$
--   the left inequality of (6).
--
--   (B.4) is the high type's incentive not to claim the low type and (B.5) the low type's incentive not to claim the high type.
-- source:
--   Lu, Can a Supplier’s Yield Risk Be Truthfully Communicated via Cheap Talk?, author manuscript of 14 July 2024 (MSOM, doi:10.1287/msom.2023.0089), OA pp. 3–4 (PDF 30–31), Online Appendix B, proof of Proposition 2, (B.4)–(B.5)

import Mathlib
import Definitions.Def_YieldCheapTalk_Truthful_Setting
open MeasureTheory

namespace YieldCheapTalk.Truthful
theorem ic_high_iff (M : Model) (hM : M.Standing) :
    (M.IC5 ↔
      ((M.Qr (M.theta .H) (M.a .H) - M.Qr (M.theta .L) (M.a .H)) * M.mu .H .H ≥
          (M.Qr (M.theta .L) (M.a .L) - M.Qr (M.theta .H) (M.a .L)) * M.mu .L .H ∧
        (M.Qr (M.theta .L) (M.a .H) - M.Qr (M.theta .H) (M.a .H)) * M.mu .H .L ≥
          (M.Qr (M.theta .H) (M.a .L) - M.Qr (M.theta .L) (M.a .L)) * M.mu .L .L)) ∧
    ((M.Qr (M.theta .H) (M.a .H) - M.Qr (M.theta .L) (M.a .H)) * M.mu .H .H ≥
          (M.Qr (M.theta .L) (M.a .L) - M.Qr (M.theta .H) (M.a .L)) * M.mu .L .H ↔
      ∑ m, M.mu m .H * M.a m ≤
        (1 + M.eta * (1 / M.theta .H + 1 / M.theta .L - 1)) * M.w) := by sorry
end YieldCheapTalk.Truthful
