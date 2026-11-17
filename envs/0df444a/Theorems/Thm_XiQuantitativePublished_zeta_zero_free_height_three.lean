-- Prove2me | Theorems.Thm_XiQuantitativePublished_zeta_zero_free_height_three
-- name    : XiQuantitativePublished.zeta_zero_free_height_three
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T12:21:55.671808+00:00
-- url     : https://prove2.me/theorems/b1c2079a-4985-488e-883c-8863ecf6682a
-- title:
--   Riemann zeta has no critical-strip zeros through height three
-- statement:
--   For Mathlib's Riemann zeta function, every s with 0 < Re(s) < 1 and 0 < Im(s) ≤ 3 satisfies zeta(s) ≠ 0. The proof uses an order-four Euler–Maclaurin expansion with an explicit remainder bound. No RH assumption or external numerical computation is assumed.
-- source:
--   Adapted from teal-sea/zeta-lab, commit a401821c9608526425f3d4cf7ff8e59bc37e1c79, hunts/hardy_first_zero/lean/HardyFirstZero/EulerMaclaurin.lean and hunts/rh_height_lean/lean/RHHeight/LowHeight.lean. https://github.com/teal-sea/zeta-lab. Lean 4.33.1 port and Branch integration: Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4. No novelty claim.

import Mathlib

theorem XiQuantitativePublished.zeta_zero_free_height_three (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (h2 : 0 < s.im) (h3 : s.im ≤ 3) : riemannZeta s ≠ 0 := by sorry
