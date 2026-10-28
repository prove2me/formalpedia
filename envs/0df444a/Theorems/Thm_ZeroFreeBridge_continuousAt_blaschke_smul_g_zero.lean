-- Prove2me | Theorems.Thm_ZeroFreeBridge_continuousAt_blaschke_smul_g_zero
-- name    : ZeroFreeBridge.continuousAt_blaschke_smul_g_zero
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:39.173972+00:00
-- url     : https://prove2.me/theorems/e30dee19-2849-4ee6-a850-b0491724f257
-- title:
--   Continuity of a canonical product at the center
-- statement:
--   Let $R>0$, let $m:\mathbb C\to\mathbb Z$ have finite support $S$ avoiding zero,
--   and let $g$ be continuous at zero. For the defined factors $F_{R,u}$, the function
--   $$z\longmapsto\left(\prod_{u\in S}F_{R,u}(z)^{-m(u)}\right)g(z)$$
--   is continuous at $z=0$. This supplies the center continuity needed for the
--   factorization argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBlaschkeCont.lean#L18-L56

import Mathlib
/- PHASE 4 (dVP frontier, the last leaf — `B·g` continuous at the centre): discharges the sole
   mechanical hypothesis of `hfac0` (`DlvpZetaCentreFac.zeta_center_factorization`).

   `B = ∏ᶠ (canonicalFactor R u)^(-m u)` is a FINITE product (finite divisor support); every factor
   `(canonicalFactor R u ·)^(-m u)` is continuous at `0` because `canonicalFactor R u` is a quotient with
   nonvanishing denominator at `0` (the zero `u ≠ 0`, so `0 - u ≠ 0`) and its value `-R/u ≠ 0` there
   (so the `zpow` is continuous, `ContinuousAt.zpow₀`).  A finite product of continuous-at-`0` factors is
   continuous at `0` (`tendsto_finsetProd`); times the analytic `g` gives `ContinuousAt (B·g) 0`.

   conjecture1_proved = False (NOT a proof of RH).
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.continuousAt_blaschke_smul_g_zero {R : ℝ} (hR : 0 < R) (m : ℂ → ℤ) {g : ℂ → ℂ}
    (hfin : (Function.support (fun u => -(m u))).Finite)
    (hsupp : ∀ u ∈ hfin.toFinset, u ≠ 0) (hg_cont0 : ContinuousAt g 0) :
    ContinuousAt ((∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) • g) 0 := by sorry
