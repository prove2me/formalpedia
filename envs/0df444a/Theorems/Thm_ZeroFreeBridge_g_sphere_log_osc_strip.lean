-- Prove2me | Theorems.Thm_ZeroFreeBridge_g_sphere_log_osc_strip
-- name    : ZeroFreeBridge.g_sphere_log_osc_strip
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:13.252987+00:00
-- url     : https://prove2.me/theorems/a0ae3187-5708-4c96-a3be-9f636d510460
-- title:
--   Boundary oscillation of the canonical zero-free factor
-- statement:
--   Let $c\in\mathbb C$ and $R>0$ satisfy $\operatorname{Re}c\ge2$,
--   $R<\operatorname{Re}c-1/2$, and $R+2\le|\operatorname{Im}c|$. Suppose $g$ gives
--   the defined canonical decomposition of $w\mapsto\zeta(c+w)$, both functions
--   are continuous on $|w|=R$, and $|\zeta(c)|\le|g(0)|$. Then for $|z|=R$,
--   $$\log|g(z)|-\log|g(0)|\le
--   \log\left(\frac{|c|+R}{|\operatorname{Im}c|-R}
--   +\frac{|c|+R}{\operatorname{Re}c-R}\right)-\log\left(2-\frac{\pi^2}{6}\right).$$
--   This transfers the zeta boundary estimate to the zero-free factor.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaSphereLogStrip.lean#L95-L119

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_canonicalDecomp_norm_eq_on_sphere
import Theorems.Thm_ZeroFreeBridge_zeta_norm_ge_two_sub
import Theorems.Thm_ZeroFreeBridge_zeta_sphere_log_bound_strip
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

theorem ZeroFreeBridge.g_sphere_log_osc_strip {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hRlt : R < c₀.re - 1/2) (himc : R + 2 ≤ |c₀.im|)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_cont : ContinuousOn (fun w => riemannZeta (c₀ + w)) (sphere 0 R))
    (hg_cont : ContinuousOn g (sphere 0 R))
    (hfg0 : ‖riemannZeta c₀‖ ≤ ‖g 0‖) :
    ∀ z ∈ sphere (0 : ℂ) R, Real.log ‖g z‖ - Real.log ‖g 0‖
      ≤ Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R))
          - Real.log (2 - Real.pi ^ 2 / 6) := by sorry
