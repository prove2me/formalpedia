-- Prove2me | Theorems.Thm_ZeroFreeBridge_htwo_shape_of_bc_sum
-- name    : ZeroFreeBridge.htwo_shape_of_bc_sum
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:55:18.860394+00:00
-- url     : https://prove2.me/theorems/92fb2c13-fbcb-4773-a4f5-601be70ded7e
-- title:
--   Dropping a nonnegative centered divisor sum
-- statement:
--   Let $c\in\mathbb C$, $R,\sigma,\gamma,A_L\in\mathbb R$, and set
--   $z=\sigma+2i\gamma$, $f(w)=\zeta(c+w)$. Suppose $\zeta$ and $f$ are meromorphic
--   on $B(c,R)$ and $B(0,R)$ respectively, and $\zeta$ is differentiable at $z$.
--   Let $S\subset B(0,R)$ be finite, with $c+S\subset B(c,R)$, and suppose
--   $$\operatorname{Re}(-\operatorname{logDeriv}f(z-c))\le A_L-
--   \operatorname{Re}\sum_{u\in S}\frac{\operatorname{div}_{B(0,R)}f(u)}{z-c-u}.$$
--   If every $\rho\in c+S$ has nonnegative divisor in $B(c,R)$ and
--   $\operatorname{Re}\rho<\sigma$, then
--   $$\operatorname{Re}\left(-\frac{\zeta'(z)}{\zeta(z)}\right)\le A_L.$$
--   This supplies the doubled-height estimate.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaBcBridge.lean#L56-L85

import Mathlib
import Theorems.Thm_ZeroFreeBridge_weighted_sum_re_nonneg
/- PHASE 4 (dVP frontier, the downstream BRIDGE): turn `bc_sum_blaschke`'s recentred output into the
   region skeleton's `hzero` input, entirely by composition of already-built lemmas.

   `bc_sum_blaschke` gives (for `f = ζ(c₀+·)`, recentred eval point `zr = (σ+γI) - c₀`)
     `-Re(logDeriv f zr) ≤ AL - Re(Σ_u divisor f (ball 0 R) u /(zr - u))`.
   `herglotz_sum_reindex` rewrites the sum to the ORIGINAL-coordinate Herglotz sum
     `Σ_ρ divisor ζ (ball c₀ R) ρ /((σ+γI) - ρ)`; `neg_logDeriv_zeta_recenter_re` rewrites the left side
   to `-deriv ζ (σ+γI)/ζ(σ+γI)`; `hzero_of_blaschke` (the Herglotz lower bound) then delivers the
   `hzero` shape `-Re(ζ'/ζ)(σ+γI) ≤ AL - k/(σ-β)` that `DlvpZetaRegion.dlvp_zeta_region` consumes.

   conjecture1_proved = False (NOT a proof of RH).
-/





open Complex MeromorphicOn

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.htwo_shape_of_bc_sum (c₀ : ℂ) (σ γ AL : ℝ) (R : ℝ)
    (hf_mero : MeromorphicOn riemannZeta (Metric.ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R))
    (s_rec : Finset ℂ)
    (hs_dom : ∀ u ∈ s_rec, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz : c₀ + ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) = (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
    (hdiff : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I))
    (hbc : (-(logDeriv (fun w => riemannZeta (c₀ + w))
                ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀))).re
             ≤ AL - (∑ u ∈ s_rec,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I - c₀) - u)).re)
    (hm : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (hlt : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), ρ.re < σ) :
    (-deriv riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)
        / riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I)).re ≤ AL := by sorry
