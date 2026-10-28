-- Prove2me | Theorems.Thm_ZeroFreeBridge_hzero_shape_of_bc_sum
-- name    : ZeroFreeBridge.hzero_shape_of_bc_sum
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:55:33.60959+00:00
-- url     : https://prove2.me/theorems/08ef9de5-7342-4abe-99e8-f3c575d75b41
-- title:
--   Extracting one zero from a centered divisor sum
-- statement:
--   Let $c\in\mathbb C$, $R,\sigma,\gamma,\beta,A_L\in\mathbb R$, and set
--   $z=\sigma+i\gamma$, $f(w)=\zeta(c+w)$. Suppose $\zeta$ and $f$ are meromorphic
--   on $B(c,R)$ and $B(0,R)$ respectively, and $\zeta$ is differentiable at $z$.
--   Let $S\subset B(0,R)$ be finite, with $c+S\subset B(c,R)$, and suppose
--   $$\operatorname{Re}(-\operatorname{logDeriv}f(z-c))\le A_L-
--   \operatorname{Re}\sum_{u\in S}\frac{\operatorname{div}_{B(0,R)}f(u)}{z-c-u}.$$
--   Suppose the divisor of $\zeta$ in $B(c,R)$ is nonnegative at every $\rho\in c+S$,
--   that $\rho_0=\beta+i\gamma$ belongs to $c+S$ with divisor $k\in\mathbb Z$, and
--   that every other $\rho\in c+S$ has $\operatorname{Re}\rho<\sigma$. Then
--   $$\operatorname{Re}\left(-\frac{\zeta'(z)}{\zeta(z)}\right)
--   \le A_L-\frac{k}{\sigma-\beta}.$$
--   Division by zero uses Lean's convention that it evaluates to zero.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaBcBridge.lean#L22-L54

import Mathlib
import Theorems.Thm_ZeroFreeBridge_herglotz_re_ge
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

theorem ZeroFreeBridge.hzero_shape_of_bc_sum (c₀ : ℂ) (σ γ β AL : ℝ) (k : ℤ) (R : ℝ)
    (hf_mero : MeromorphicOn riemannZeta (Metric.ball c₀ R))
    (hf'_mero : MeromorphicOn (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R))
    (s_rec : Finset ℂ)
    (hs_dom : ∀ u ∈ s_rec, u ∈ Metric.ball (0 : ℂ) R ∧ c₀ + u ∈ Metric.ball c₀ R)
    (hcz : c₀ + ((σ : ℂ) + (γ : ℂ) * I - c₀) = (σ : ℂ) + (γ : ℂ) * I)
    (hdiff : DifferentiableAt ℂ riemannZeta ((σ : ℂ) + (γ : ℂ) * I))
    (hbc : (-(logDeriv (fun w => riemannZeta (c₀ + w)) ((σ : ℂ) + (γ : ℂ) * I - c₀))).re
             ≤ AL - (∑ u ∈ s_rec,
                 (divisor (fun w => riemannZeta (c₀ + w)) (Metric.ball 0 R) u : ℂ)
                   / (((σ : ℂ) + (γ : ℂ) * I - c₀) - u)).re)
    (hm : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), 0 ≤ divisor riemannZeta (Metric.ball c₀ R) ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s_rec.image (fun u => c₀ + u)) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I)
    (hmρ₀ : divisor riemannZeta (Metric.ball c₀ R) ρ₀ = k)
    (hother : ∀ ρ ∈ s_rec.image (fun u => c₀ + u), ρ ≠ ρ₀ → ρ.re < σ) :
    (-deriv riemannZeta ((σ : ℂ) + (γ : ℂ) * I) / riemannZeta ((σ : ℂ) + (γ : ℂ) * I)).re
      ≤ AL - (k : ℝ) / (σ - β) := by sorry
