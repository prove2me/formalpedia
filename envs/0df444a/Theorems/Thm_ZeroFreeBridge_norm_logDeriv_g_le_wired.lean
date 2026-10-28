-- Prove2me | Theorems.Thm_ZeroFreeBridge_norm_logDeriv_g_le_wired
-- name    : ZeroFreeBridge.norm_logDeriv_g_le_wired
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:09:36.577241+00:00
-- url     : https://prove2.me/theorems/d351ad5b-2ef6-4a9d-b0b5-1557e8018ba6
-- title:
--   Explicit interior bound for a canonical zeta factor
-- statement:
--   Let $c\in\mathbb C$ and $R>0$ satisfy $\operatorname{Re}c\ge2$,
--   $R<\operatorname{Re}c-1/2$, and $R+2\le|\operatorname{Im}c|$. Let $g$ be the
--   zero-free factor in the defined canonical decomposition of $w\mapsto\zeta(c+w)$
--   on $B(0,R)$, and let $|z_0|<R$. Define
--   $$M=\log\left(\frac{|c|+R}{|\operatorname{Im}c|-R}
--   +\frac{|c|+R}{\operatorname{Re}c-R}\right)-\log\left(2-\frac{\pi^2}{6}\right).$$
--   Then
--   $$|\operatorname{logDeriv}g(z_0)|\le\frac{4M(R+|z_0|)}{(R-|z_0|)^2}.$$
--   This assembles the boundary and canonical-factor estimates.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaGBound.lean#L28-L96

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_continuousAt_blaschke_smul_g_zero
import Theorems.Thm_ZeroFreeBridge_norm_blaschke_center_le_one
import Theorems.Thm_ZeroFreeBridge_norm_logDeriv_g_le_strip
import Theorems.Thm_ZeroFreeBridge_zeta_center_factorization
/- PHASE 4 (dVP frontier, item 1 COMPLETE — hg_bound fully wired): the entire-part bound
   `‖logDeriv g z₀‖ ≤ 4·Aζ''·(R+‖z₀‖)/(R-‖z₀‖)² = O(L)` for the recentred-ζ Blaschke quotient g,
   from JUST a `CanonicalDecomp` + the disk geometry — every sub-input discharged internally.

   `norm_logDeriv_g_le_strip` needs 4 inputs beyond D/geometry: hf_cont, hg_cont, hg_dcc, hfg0.
   This wrapper discharges all four (general in c₀, so reusable for the height-γ disk c₀=2+iγ AND
   the height-2γ disk c₁=2+2iγ):
     * hf_cont  = `zeta_recenter_cont_sphere` (ζ(c₀+·) cont on sphere);
     * hg_cont  = `canonicalDecomp_contOn_sphere`, hg_dcc = `canonicalDecomp_diffContOnCl`
                  (g analytic up to the sphere, PR #289, needs f analytic on the sphere);
     * hfg0     = `zeta_norm_le_g_zero` (‖ζ c₀‖≤‖g 0‖ from ‖B 0‖≤1), fed by the centre factorization
                  `zeta_center_factorization` ← `continuousAt_blaschke_smul_g_zero` (B·g cont at 0) +
                  the divisor-support facts (u≠0 since ζ(c₀)≠0 ⟹ divisor 0 =0; ‖u‖<R; divisor ≥0).
   `1∉closedBall c₀ R` is derived from `|c₀.im| ≥ R+2`; the recentred ζ analyticity on closedBall 0 R
   is the standard `zeta_analyticOnNhd_disk ∘ shift`.  conjecture1_proved = False (NOT a proof of RH).
-/







open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.norm_logDeriv_g_le_wired {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hR : 0 < R) (hc2 : 2 ≤ c₀.re) (hRlt : R < c₀.re - 1/2) (himc : R + 2 ≤ |c₀.im|)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < R) :
    ‖logDeriv g z₀‖
      ≤ 4 * (Real.log ((‖c₀‖ + R) / (|c₀.im| - R) + (‖c₀‖ + R) / (c₀.re - R))
              - Real.log (2 - Real.pi ^ 2 / 6))
          * (R + ‖z₀ - 0‖) / (R - ‖z₀ - 0‖) ^ 2 := by sorry
