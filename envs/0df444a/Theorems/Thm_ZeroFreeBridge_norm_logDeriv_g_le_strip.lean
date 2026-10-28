-- Prove2me | Theorems.Thm_ZeroFreeBridge_norm_logDeriv_g_le_strip
-- name    : ZeroFreeBridge.norm_logDeriv_g_le_strip
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:05:14.621422+00:00
-- url     : https://prove2.me/theorems/249cc481-b4bc-484d-a1b5-c07446759d49
-- title:
--   Interior bound from the zero-free factor boundary
-- statement:
--   Let $c\in\mathbb C$ and $R>0$ satisfy $\operatorname{Re}c\ge2$,
--   $R<\operatorname{Re}c-1/2$, and $R+2\le|\operatorname{Im}c|$. Suppose $g$
--   gives the defined canonical decomposition of $w\mapsto\zeta(c+w)$, both are
--   continuous on $|w|=R$, $g$ is holomorphic in the disk, continuous on its
--   closure and nonzero in it, and $|\zeta(c)|\le|g(0)|$. Define
--   $$M=\log\left(\frac{|c|+R}{|\operatorname{Im}c|-R}
--   +\frac{|c|+R}{\operatorname{Re}c-R}\right)-\log\left(2-\frac{\pi^2}{6}\right).$$
--   Then for $|z_0|<R$,
--   $$|\operatorname{logDeriv}g(z_0)|\le\frac{4M(R+|z_0|)}{(R-|z_0|)^2}.$$
--   This is the interior entire-factor estimate.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaSphereLogStrip.lean#L121-L152

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_g_sphere_log_osc_strip
import Theorems.Thm_ZeroFreeBridge_norm_logDeriv_le_of_sphere_log_norm_le_interior
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

theorem ZeroFreeBridge.norm_logDeriv_g_le_strip {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hRlt : R < c₀.re - 1/2) (himc : R + 2 ≤ |c₀.im|)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_cont : ContinuousOn (fun w => riemannZeta (c₀ + w)) (sphere 0 R))
    (hg_cont : ContinuousOn g (sphere 0 R))
    (hg_dcc : DiffContOnCl ℂ g (ball 0 R)) (hg_ne : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0)
    (hfg0 : ‖riemannZeta c₀‖ ≤ ‖g 0‖) {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) :
    ‖logDeriv g z₀‖
      ≤ 4 * (Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R))
              - Real.log (2 - Real.pi ^ 2 / 6))
          * (R + ‖z₀ - 0‖) / (R - ‖z₀ - 0‖) ^ 2 := by sorry
