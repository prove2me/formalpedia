-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta_sphere_bound_strip
-- name    : ZeroFreeBridge.zeta_sphere_bound_strip
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:57.117418+00:00
-- url     : https://prove2.me/theorems/5ea1d4de-8a16-4e04-82d1-af6a993bbd5c
-- title:
--   Zeta norm bound on a circle crossing the strip
-- statement:
--   Let $c\in\mathbb C$ and $R>0$ satisfy $R<\operatorname{Re}c-1/2$ and
--   $R+2\le|\operatorname{Im}c|$. For each $|z-c|=R$,
--   $$|\zeta(z)|\le\frac{|c|+R}{|\operatorname{Im}c|-R}
--   +\frac{|c|+R}{\operatorname{Re}c-R}.$$
--   The estimate permits part of the circle to lie to the left of $\operatorname{Re}z=1$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaCountStrip.lean#L21-L58

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_differentiableAt_fractIntegral
import Theorems.Thm_ZeroFreeBridge_isPreconnected_stripDomain
import Theorems.Thm_ZeroFreeBridge_zeta_fract_repr_of
import Theorems.Thm_ZeroFreeBridge_zeta_repr_R1
import Theorems.Thm_ZeroFreeBridge_zeta_repr_integral_bound
/- PHASE 4 (dVP frontier, item 3 input — strip-capable Jensen zero count): the version of
   `zeta_zero_count_unconditional` (`DlvpZetaDisk`) that survives the disk DIPPING BELOW `Re = 1`.

   The count `∑ divisor ≤ log(M/‖ζ c‖)/log(R/r)` (`zeta_zero_count_le`) takes the boundary bound `M`
   as a HYPOTHESIS and only needs `1 < c.re` at the CENTER plus `1 ∉ closedBall c |R|` — ζ is
   analytic on ANY disk avoiding `s = 1`, even one reaching `Re < 1`.  The original
   `zeta_zero_count_unconditional` supplies `M` via `zeta_sphere_bound` (`Re > 1`), forcing
   `|R| + 1 < c.re`.  Here we supply `M` via `zeta_strip_bound` (valid on the FULL strip
   `Re > 0`, `s ≠ 1`), so the disk may enclose a nontrivial zero `ρ₀` (`Re < 1`).

   This delivers the `O(L)` zero-count bound `∑ |divisor| ≤ Ccount·L` that `hAL_arith` (`DlvpHALArith`)
   consumes.  conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.zeta_sphere_bound_strip (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hRlt : R < c.re - 1/2) (himc : R + 2 ≤ |c.im|)
    {z : ℂ} (hz : z ∈ sphere c R) :
    ‖riemannZeta z‖ ≤ (‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R) := by sorry
