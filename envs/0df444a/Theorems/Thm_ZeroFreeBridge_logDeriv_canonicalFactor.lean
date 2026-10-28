-- Prove2me | Theorems.Thm_ZeroFreeBridge_logDeriv_canonicalFactor
-- name    : ZeroFreeBridge.logDeriv_canonicalFactor
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:44:48.652434+00:00
-- url     : https://prove2.me/theorems/e5c630d4-3010-4dbf-9645-ce196ff9be6d
-- title:
--   Logarithmic derivative of a canonical factor
-- statement:
--   Let $R\in\mathbb R\setminus\{0\}$ and $w,z\in\mathbb C$ satisfy $z\ne w$ and
--   $R^2-\overline w z\ne0$. For the defined canonical factor $F_{R,w}$,
--   $$\operatorname{logDeriv}F_{R,w}(z)
--   =-\frac{\overline w}{R^2-\overline w z}-\frac1{z-w}.$$
--   This identity gives the individual terms in the zero-sum decomposition.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpCanonicalLogDeriv.lean#L20-L37

import Mathlib
/- PHASE 4 (dVP frontier, BLASCHKE item (d) FOUNDATION): the log-derivative of the canonical factor.

   Item (d) revises the obligation-(i) Herglotz sum from the monomial `1/(z-ρ)` to the canonical
   (Blaschke) factor.  `canonicalFactor R w z = (R² - conj w · z)/(R(z-w))` is a ratio of affine
   functions, so its log-derivative is the difference of the two affine log-derivatives:

     `logDeriv (canonicalFactor R w) z = -conj w/(R² - conj w · z) - 1/(z-w)`.

   The `-1/(z-w)` term is exactly the monomial Herglotz contribution (with sign fixed by the
   `-divisor` exponent in the Blaschke product); the extra `-conj w/(R² - conj w · z)` term is the
   BOUNDED correction (its pole `R²/conj w` lies OUTSIDE the disk), which gets absorbed into the
   O(L) entire-part bound.  Function-agnostic.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.logDeriv_canonicalFactor {R : ℝ} {w z : ℂ} (hR : R ≠ 0)
    (hnum : (R : ℂ) ^ 2 - (starRingEnd ℂ) w * z ≠ 0) (hzw : z - w ≠ 0) :
    logDeriv (canonicalFactor R w) z
      = -(starRingEnd ℂ) w / ((R : ℂ) ^ 2 - (starRingEnd ℂ) w * z) - 1 / (z - w) := by sorry
