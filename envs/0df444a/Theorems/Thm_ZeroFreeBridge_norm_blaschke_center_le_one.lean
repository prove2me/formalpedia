-- Prove2me | Theorems.Thm_ZeroFreeBridge_norm_blaschke_center_le_one
-- name    : ZeroFreeBridge.norm_blaschke_center_le_one
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:14.542829+00:00
-- url     : https://prove2.me/theorems/2944be80-d98e-4f72-a569-0e1e318da2e9
-- title:
--   Canonical-product bound at the center
-- statement:
--   Let $R>0$ and $m:\mathbb C\to\mathbb Z$ have finite support $S$, with
--   $0<|u|<R$ and $m(u)\ge0$ for each $u\in S$. For the defined factors $F_{R,u}$,
--   $$\left|\prod_{u\in S}F_{R,u}(0)^{-m(u)}\right|\le1.$$
--   This supplies the center estimate for the canonical product.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBlaschkeCenter.lean#L40-L62

import Mathlib
/- PHASE 4 (dVP frontier, the Blaschke-CENTRE relation ‖B 0‖ ≤ 1 — item 2's last piece): the canonical
   Blaschke factor has modulus `R/‖w‖ > 1` at the centre, so raised to `-divisor` (`divisor ≥ 0` since the
   disk avoids the ζ pole) each factor has modulus `≤ 1`, and the finite product `‖B 0‖ ≤ 1`.

   Combined with the centre factorization `‖ζ c₀‖ = ‖f 0‖ = ‖B 0‖·‖g 0‖` this gives the Blaschke-centre
   relation `‖ζ c₀‖ ≤ ‖g 0‖` that `DlvpZetaEntire.norm_logDeriv_g_le` requires.  This file supplies the
   per-factor computational core.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.norm_blaschke_center_le_one {R : ℝ} (hR : 0 < R) (m : ℂ → ℤ)
    (hfin : (Function.support (fun u => -(m u))).Finite)
    (hsupp : ∀ u ∈ hfin.toFinset, u ≠ 0 ∧ ‖u‖ < R)
    (hm : ∀ u ∈ hfin.toFinset, 0 ≤ m u) :
    ‖(∏ᶠ u, (canonicalFactor R u) ^ (-(m u))) 0‖ ≤ 1 := by sorry
