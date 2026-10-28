-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta_logderiv_eq
-- name    : ZeroFreeBridge.zeta_logderiv_eq
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:54:23.654395+00:00
-- url     : https://prove2.me/theorems/ac40c266-23d6-4644-aea7-dbb82def6b72
-- title:
--   Logarithmic derivative split at the zeta pole
-- statement:
--   Let $s\in\mathbb C\setminus\{1\}$ and suppose the defined regularized zeta
--   function $\zeta_1(s)$ is nonzero. Then
--   $$\frac{\zeta'(s)}{\zeta(s)}=-\frac1{s-1}+\frac{\zeta_1'(s)}{\zeta_1(s)}.$$
--   The identity isolates the pole contribution at $s=1$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaPoleEffective.lean#L97-L111

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
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

theorem ZeroFreeBridge.zeta_logderiv_eq {s : ℂ} (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s
      = -(s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by sorry
