-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta_sphere_log_bound_strip
-- name    : ZeroFreeBridge.zeta_sphere_log_bound_strip
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:14.637551+00:00
-- url     : https://prove2.me/theorems/12a6b62c-3c85-4b05-b6d9-ac76da91766c
-- title:
--   Zeta logarithmic oscillation on a shifted circle
-- statement:
--   Let $c\in\mathbb C$ and $R>0$ satisfy $\operatorname{Re}c\ge2$,
--   $R<\operatorname{Re}c-1/2$, and $R+2\le|\operatorname{Im}c|$. For $|z-c|=R$,
--   $$\log|\zeta(z)|-\log|\zeta(c)|\le
--   \log\left(\frac{|c|+R}{|\operatorname{Im}c|-R}
--   +\frac{|c|+R}{\operatorname{Re}c-R}\right)-\log\left(2-\frac{\pi^2}{6}\right).$$
--   The bound supplies the logarithmic oscillation on the outer circle.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaSphereLogStrip.lean#L26-L93

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_differentiableAt_fractIntegral
import Theorems.Thm_ZeroFreeBridge_isPreconnected_stripDomain
import Theorems.Thm_ZeroFreeBridge_zeta_fract_repr_of
import Theorems.Thm_ZeroFreeBridge_zeta_norm_ge_two_sub
import Theorems.Thm_ZeroFreeBridge_zeta_repr_R1
import Theorems.Thm_ZeroFreeBridge_zeta_repr_integral_bound
/- PHASE 4 (dVP frontier, brick 3 — strip-capable ζ boundary oscillation): the version of
   `zeta_sphere_log_bound` / `g_sphere_log_osc` that survives the sphere DIPPING BELOW `Re = 1`.

   The original `zeta_sphere_log_bound` (`DlvpZetaSphereLog`) needs `R + 1 < c.re`, so the whole
   sphere stays in `Re > 1` — but then the disk cannot enclose a nontrivial zero `ρ₀` (which has
   `Re < 1`).  The KEY observation: `zeta_strip_bound` (`StripBound`) already holds on ALL of
   `stripDomain = {Re > 0} \ {1}` (NOT just `Re > 1`) — so the upper bound `‖ζ z‖ ≤ ‖z‖/‖z-1‖ +
   ‖z‖/Re z` is available on the sub-1 strip too.  We relax the hypothesis to `R < c.re - 1/2`
   (sphere stays in `Re > 1/2 > 0`) plus `R + 2 ≤ |c.im|` (sphere stays off `s = 1`, and `‖z-1‖`
   is large), and — since `ζ` MAY now vanish on the sphere — handle `Real.log ‖ζ z‖` at a zero by
   `Real.log 0 = 0 ≤ log U''` (the upper constant `U'' ≥ 1`).  The oscillation bound is unchanged
   in spirit: `log‖ζ z‖ - log‖ζ c‖ ≤ log U'' - log(2 - π²/6) = O(log|c|) = O(L)`.

   conjecture1_proved = False (NOT a proof of RH).
-/






open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.zeta_sphere_log_bound_strip (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hc2 : 2 ≤ c.re) (hRlt : R < c.re - 1/2) (himc : R + 2 ≤ |c.im|)
    {z : ℂ} (hz : z ∈ sphere c R) :
    Real.log ‖riemannZeta z‖ - Real.log ‖riemannZeta c‖
      ≤ Real.log ((‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R))
        - Real.log (2 - Real.pi ^ 2 / 6) := by sorry
