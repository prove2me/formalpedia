-- Prove2me | Theorems.Thm_ZeroFreeBridge_weighted_sum_re_nonneg
-- name    : ZeroFreeBridge.weighted_sum_re_nonneg
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:47:27.378596+00:00
-- url     : https://prove2.me/theorems/89ced03c-0945-45df-8adf-1cb185473156
-- title:
--   Nonnegativity of a weighted zero sum
-- statement:
--   Let $S\subset\mathbb C$ be finite, $m:S\to\mathbb Z$ nonnegative, and
--   $z\in\mathbb C$ satisfy $\operatorname{Re}\rho<\operatorname{Re}z$ for every
--   $\rho\in S$. Then
--   $$\operatorname{Re}\sum_{\rho\in S}\frac{m(\rho)}{z-\rho}\ge0.$$
--   This allows all such terms in the zero sum to be discarded in a lower bound.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBlaschkeToSkeleton.lean#L17-L32

import Mathlib
/- PHASE 4 (dVP frontier, Blaschke → skeleton GLUE): combine the Blaschke BC-SUM with the Herglotz
   lower bound to produce the reduction skeleton's `hzero` / `htwo` shapes.

   `DlvpBCSumBlaschke.bc_sum_blaschke` gives `-Re(ζ'/ζ)(z) ≤ AL - Re(Z)`, `Z = Σ_ρ (m ρ)/(z-ρ)`.
   `DlvpHerglotzLower.herglotz_re_ge` gives `Re(Z) ≥ k/(σ-β)` (keep the equal-height zero, drop the
   rest).  A `linarith` combines them into `-Re(ζ'/ζ)(z) ≤ AL - k/(σ-β)` — the exact `hzero` input of
   `DlvpPole.dlvp_region_of_bc_inputs`.  Dropping ALL zeros (`Re(Z) ≥ 0`, `weighted_sum_re_nonneg`)
   instead gives the `htwo` shape `-Re(ζ'/ζ)(z) ≤ AL`.  Abstract in the function `f` (composes with the
   ζ recentering).  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.weighted_sum_re_nonneg (s : Finset ℂ) (m : ℂ → ℤ) (z : ℂ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ) (hlt : ∀ ρ ∈ s, ρ.re < z.re) :
    0 ≤ (∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ)).re := by sorry
