-- Prove2me | Theorems.Thm_ZeroFreeBridge_logDeriv_eq_herglotz_add_entire
-- name    : ZeroFreeBridge.logDeriv_eq_herglotz_add_entire
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:54.621625+00:00
-- url     : https://prove2.me/theorems/377ef53b-5574-418f-9189-a97d66bcce22
-- title:
--   Logarithmic derivative as a zero sum and correction
-- statement:
--   Let $R>0$, and suppose $f$ and $g$ have the defined canonical decomposition on
--   $B(0,R)$, are analytic near the disk, and $g$ is zero-free there. Let $S$ be the
--   finite support of $-\operatorname{div}(f)$ in the disk, and take $z$ in the disk
--   outside $S$. With $m(u)=\operatorname{div}(f)(u)$,
--   $$\operatorname{logDeriv}f(z)=\sum_{u\in S}\frac{m(u)}{z-u}
--   +\sum_{u\in S}\frac{m(u)\overline u}{R^2-\overline u z}
--   +\operatorname{logDeriv}g(z).$$
--   The first sum records the zeros; the second is the canonical-factor correction.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBlaschkeSplitExpand.lean#L20-L61

import Mathlib
import Theorems.Thm_ZeroFreeBridge_logDeriv_canonicalFactor
import Theorems.Thm_ZeroFreeBridge_logDeriv_split_off_zeros
/- PHASE 4 (dVP frontier, BLASCHKE item (d4) core): the ζ log-derivative in Herglotz + entire-part
   form, with the canonical (Blaschke) factors.

   Expanding `DlvpBlaschkeSplit.logDeriv_split_off_zeros` via `DlvpCanonicalLogDeriv.logDeriv_
   canonicalFactor` and `n u = -divisor u` gives the dVP explicit-formula shape:

     `logDeriv ζ z = Σ_ρ (divisor ρ)/(z-ρ)  +  [ Σ_ρ (divisor ρ)·conj ρ/(R²-conj ρ·z) + logDeriv g z ]`,

   i.e. `ζ'/ζ = Z + E` with `Z` the Herglotz zero-sum (Re ≥ 0 near the line, droppable) and the entire
   part `E` = correction + `logDeriv g` bounded `O(L)` by `DlvpCorrectionBound` + item (c).  This is
   exactly the `w = Z + E` input to the reduction skeleton `DlvpBCSum`.  conjecture1_proved = False.
-/



open Complex Metric MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.logDeriv_eq_herglotz_add_entire {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (D : CanonicalDecomp f g R)
    (hf_ana : AnalyticOnNhd ℂ f (ball 0 R)) (hg_ana : AnalyticOnNhd ℂ g (ball 0 R))
    (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hzne : ∀ u ∈ hfin.toFinset, z ≠ u) :
    logDeriv f z
      = (∑ u ∈ hfin.toFinset, (divisor f (ball 0 R) u : ℂ) / (z - u))
        + ((∑ u ∈ hfin.toFinset,
              (divisor f (ball 0 R) u : ℂ) * (starRingEnd ℂ) u
                / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * z))
           + logDeriv g z) := by sorry
