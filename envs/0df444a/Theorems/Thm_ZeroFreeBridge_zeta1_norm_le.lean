-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta1_norm_le
-- name    : ZeroFreeBridge.zeta1_norm_le
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:59.437493+00:00
-- url     : https://prove2.me/theorems/765c6a9e-9d0c-466f-81a3-4f4f366ce06f
-- title:
--   Bound for the regularized zeta function near one
-- statement:
--   Let $\zeta_1$ denote the defined regularized zeta function. If $|z-1|\le1/2$,
--   then
--   $$|\zeta_1(z)|\le3.$$
--   This is the outer-disk bound used for the pole estimate.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaPoleEffective.lean#L27-L56

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_differentiableAt_fractIntegral
import Theorems.Thm_ZeroFreeBridge_isPreconnected_stripDomain
import Theorems.Thm_ZeroFreeBridge_zeta_fract_repr_of
import Theorems.Thm_ZeroFreeBridge_zeta_repr_R1
import Theorems.Thm_ZeroFreeBridge_zeta_repr_integral_bound
/- PHASE 4 (dVP frontier, the EFFECTIVE pole bound): replace Mathlib's non-effective pole constant
   (`log_deriv_riemannZeta_add_inv_sub_bounded`, a bare `∃`) with an EXPLICIT one.

   The only non-effective input to `dlvp_zeta_region_rate`'s constant `c` is the pole bound
   `Re(-ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + A₀` near `σ = 1`.  This file makes it explicit with
   `A₀ = 16`, `ε₀ = 1/48`, via a Cauchy estimate on `ζ₁ := (·-1)·ζ` (Mathlib `riemannZeta₁`,
   entire, `ζ₁ 1 = 1`, `ζ = (s-1)⁻¹·ζ₁`):

     * `zeta1_norm_le`   `‖ζ₁ z‖ ≤ 3` on `closedBall 1 (1/2)` — via the explicit `zeta_strip_bound`;
     * `zeta1_deriv_le`  `‖ζ₁' w‖ ≤ 12` on `closedBall 1 (1/4)` — Cauchy estimate (radius 1/4);
     * `zeta1_lower`     `‖ζ₁ σ‖ ≥ 3/4` for `σ-1 ≤ 1/48` — mean-value bound `‖ζ₁ σ - 1‖ ≤ 12(σ-1)`;
     * `zeta_logderiv_eq`  `ζ'/ζ = -(s-1)⁻¹ + ζ₁'/ζ₁` at an explicit point (`s≠1`, `ζ₁ s≠0`);
     * `hpole_effective`   `Re(-ζ'/ζ(σ)) ≤ Re(1/(σ-1)) + 16` for `1 < σ`, `σ-1 < 1/48`
       (`|ζ₁'/ζ₁| ≤ 12/(3/4) = 16`).

   Feeding this into the rate construction makes `c = 1/(112·(16 + 48 + E))` a CONCRETE positive
   real (`E` the explicit constant from `dlvp_zeta_region_rate`).  The dVP constant is now effective.
   conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.zeta1_norm_le {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) (1/2)) : ‖riemannZeta₁ z‖ ≤ 3 := by sorry
