-- Prove2me | Theorems.Thm_ZeroFreeBridge_differentiableAt_fractIntegral
-- name    : ZeroFreeBridge.differentiableAt_fractIntegral
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:52:46.817378+00:00
-- url     : https://prove2.me/theorems/7d39e5bb-c086-4290-bae3-913cc0e76297
-- title:
--   Differentiability of the fractional-part integral
-- statement:
--   For every $z\in\mathbb C$ with $\operatorname{Re}z>0$, the defined function
--   $\operatorname{fractIntegral}$ is complex differentiable at $z$:
--   $$\operatorname{DifferentiableAt}_{\mathbb C}(\operatorname{fractIntegral},z).$$
--   This gives the analytic input to the fractional-part continuation.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/StripReprR2.lean#L22-L178

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Mathlib
/- (R2) DISCHARGE for `zeta_fract_repr_of`: the RHS integral

       fractIntegral s = ∫ x in Ioi 1, {x} · x^{-(s+1)} dx

   is complex-differentiable in `s` on the open right half-plane `{0 < Re s}`.
   This removes the `DifferentiableAt ℂ fractIntegral z` hypothesis (R2).

   Differentiation under the integral sign, via
   `hasDerivAt_integral_of_dominated_loc_of_lip`.  Parameter-derivative
   `F'(x) = {x} · (−log x) · x^{-(z+1)}`; on the neighbourhood `S = {z.re/2 < Re w}`
   the modulus of the w-derivative is dominated by `log x · x^{-(z.re/2 + 1)}`,
   integrable on `(1,∞)` because `z.re/2 > 0`.

   A gap-filler FEEDING input (R); NOT a proof of RH.  conjecture1_proved = False.
-/


open Set MeasureTheory Filter Topology

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.differentiableAt_fractIntegral {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ fractIntegral z := by sorry
