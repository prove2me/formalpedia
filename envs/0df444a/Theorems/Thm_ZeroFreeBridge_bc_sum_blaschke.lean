-- Prove2me | Theorems.Thm_ZeroFreeBridge_bc_sum_blaschke
-- name    : ZeroFreeBridge.bc_sum_blaschke
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:55.030716+00:00
-- url     : https://prove2.me/theorems/c43276bc-7653-4a71-91e0-08a34aeecd91
-- title:
--   Canonical-factor bound for the logarithmic derivative
-- statement:
--   Let $R>0$, and suppose $f$ and $g$ have the defined canonical decomposition on
--   $B(0,R)$, are analytic near that disk, and $g$ has no zeros there. Let $S$ be
--   the finite support of the negative divisor of $f$ in the disk. For $z\in B(0,R)$
--   outside $S$, put $m(u)=\operatorname{div}(f)(u)$. If $|g'(z)/g(z)|\le B_g$ and
--   $$\frac{\sum_{u\in S}|m(u)|}{R-|z|}+B_g\le A_L,$$
--   then
--   $$\operatorname{Re}(-f'(z)/f(z))\le A_L-
--   \operatorname{Re}\sum_{u\in S}\frac{m(u)}{z-u}.$$
--   This is the zero-sum estimate used in the zero-free-region argument.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBCSumBlaschke.lean#L21-L50

import Mathlib
import Theorems.Thm_ZeroFreeBridge_logDeriv_eq_herglotz_add_entire
import Theorems.Thm_ZeroFreeBridge_norm_correction_sum_le
/- PHASE 4 (dVP frontier, BLASCHKE item (d4) capstone): the BC-SUM for the Blaschke split.

   Combines the explicit formula `ζ'/ζ = Z + E` (`DlvpBlaschkeSplitExpand`) with the entire-part
   bound `‖E‖ ≤ A·L` (correction via `DlvpCorrectionBound` (d3) + `‖logDeriv g‖` via item (c)) through
   the rung-2 combine `DlvpBCSum.bc_sum_of_split`, yielding the de la Vallee Poussin BC-SUM:

     `-Re(ζ'/ζ)(z) ≤ A·L − Re(Σ_ρ (divisor ρ)/(z−ρ))`,

   with `Z = Σ_ρ (divisor ρ)/(z−ρ)` the Herglotz zero-sum whose `Re` is `≥ 0` near the line (rung 1),
   hence droppable.  This is the `hzero`/`htwo` input the reduction skeleton (`DlvpZeroSum`/`DlvpPole`/
   `DlvpBCSum` → `ZeroFreeRegion`) consumes to reach `β ≤ 1 − c/log|t|`.  conjecture1_proved = False.
-/




open Complex Metric MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.bc_sum_blaschke {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R)
    (hf_ana : AnalyticOnNhd ℂ f (ball 0 R)) (hg_ana : AnalyticOnNhd ℂ g (ball 0 R))
    (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hzne : ∀ u ∈ hfin.toFinset, z ≠ u)
    {Bg AL : ℝ} (hg_bound : ‖logDeriv g z‖ ≤ Bg)
    (hAL : (∑ u ∈ hfin.toFinset, |(divisor f (ball 0 R) u : ℝ)|) / (R - ‖z‖) + Bg ≤ AL) :
    (-(logDeriv f z)).re
      ≤ AL - (∑ u ∈ hfin.toFinset, (divisor f (ball 0 R) u : ℂ) / (z - u)).re := by sorry
