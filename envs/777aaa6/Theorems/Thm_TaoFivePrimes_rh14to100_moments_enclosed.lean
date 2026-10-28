-- Prove2me | Theorems.Thm_TaoFivePrimes_rh14to100_moments_enclosed
-- name    : TaoFivePrimes.rh14to100_moments_enclosed
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T09:51:59.669838+00:00
-- url     : https://prove2.me/theorems/1133de2e-7a20-4ee9-b4cb-01410062dc57
-- title:
--   RH height 14–100 — certified Mellin moment enclosures
-- statement:
--   For each j from 0 through 255, the actual scaled even Mellin moment of the Riemann-zeta theta kernel differs from the proposed rounded value by at most 10^(-46). The actual moment integrates t^(-3/4) (64 log t)^(2j)/(2j)! times (the even theta kernel at zero minus one) over t > 1. The proposed value is the original certificate integer numerator divided by 10^64. These are the global moment enclosures used by the existing height-14–100 RH pilot.
--
--   Writing the actual moment as $M_j$ and the stored integer as $C_j$, the assertion is
--
--   $$|M_j-C_j/10^{64}|\le 10^{-46},\qquad 0\le j<256.$$
--
--   These estimates supply the global polynomial input to the existing height-14–100 pilot; they do not assert RH at higher heights.
--
--   **Port note.** Port to the Mathlib `777aaa6` / Lean v4.29.0-rc3 environment of the Riemann Hypothesis mission of the theorem `TaoFivePrimes.rh14to100_moments_enclosed` (id `c8862379-7ebd-45e7-8271-314543d5c71e`, env `0df444a`), whose statement and certificate are due to @raresbuhai, adapting @sometik179's height-14–100 proof (submission c9908072-d99a-4431-aad8-a72c6352619a). The statement is unchanged; it refers to the ported definitions of the same names in this environment.
-- source:
--   sometik179, Prove2Me height-14–100 certificate c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03), https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a, GlobalMomentEnclosure module, moments_enclosed. Original theta/Mellin foundations attributed to Gabewhigham. The same bound and proposed integers occur in the publicly submitted locally verified pilot.; ported from 0df444a theorem c8862379-7ebd-45e7-8271-314543d5c71e

import Definitions.Def_TaoFivePrimes_RH14To100MomentModel

theorem TaoFivePrimes.rh14to100_moments_enclosed (j : ℕ) (hj : j<256) :
    |CertifiedGlobalMoments.moment j-CertifiedGlobalMomentEnclosure.candidateMoment j|≤ 1/10^46 := by sorry
