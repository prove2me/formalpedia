-- Prove2me | Theorems.Thm_ZeroFreeBridge_herglotz_re_ge
-- name    : ZeroFreeBridge.herglotz_re_ge
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:44:48.611773+00:00
-- url     : https://prove2.me/theorems/7cc36c4f-c2f4-4df2-9c8b-1ad5b5e27973
-- title:
--   Lower bound from one term of a zero sum
-- statement:
--   Let $S\subset\mathbb C$ be finite and $m:S\to\mathbb Z$ nonnegative. Let
--   $\rho_0=\beta+i\gamma\in S$ have weight $k=m(\rho_0)$, and suppose every other
--   $\rho\in S$ has $\operatorname{Re}\rho<\sigma$. Then
--   $$\frac{k}{\sigma-\beta}\le\operatorname{Re}
--   \sum_{\rho\in S}\frac{m(\rho)}{\sigma+i\gamma-\rho}.$$
--   The singled-out zero gives a lower bound for the weighted zero sum.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpHerglotzLower.lean#L21-L47

import Mathlib
/- PHASE 4 (dVP frontier, BLASCHKE → skeleton bridge): the Herglotz lower bound.

   `DlvpBCSumBlaschke.bc_sum_blaschke` gives `-Re(ζ'/ζ) ≤ A·L − Re(Z)` with `Z = Σ_ρ (divisor ρ)/(z−ρ)`.
   To reach the skeleton's `hzero` shape `-Re(ζ'/ζ) ≤ A·L − k/(σ−β)`, one needs `Re(Z) ≥ k/(σ−β)`:
   keep the zero `ρ₀ = β+γI` at the SAME height as `z = σ+γI` (its real part is exactly `k/(σ−β)`,
   rung 1 `re_smul_inv_sub_at_equal_height`) and DROP the other zeros (each `Re ≥ 0` since their real
   part is `< σ`, rung 1 `re_inv_sub_nonneg_of_re_lt`, times the nonnegative multiplicity).

     `herglotz_re_ge` :  ρ₀ ∈ s with `ρ₀ = β+γI`, `m ρ₀ = k`, `m ≥ 0`, other zeros `Re < σ`
       ⟹  `k/(σ−β) ≤ Re(Σ_ρ (m ρ)/((σ+γI) − ρ))`.

   Combined with `bc_sum_blaschke` (a `linarith`) this yields the `hzero`/`htwo` inputs the reduction
   skeleton `DlvpPole.dlvp_region_of_bc_inputs` consumes.  conjecture1_proved = False (NOT RH).
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.herglotz_re_ge {s : Finset ℂ} (m : ℂ → ℤ) (σ γ β : ℝ) (k : ℤ)
    (hm : ∀ ρ ∈ s, 0 ≤ m ρ)
    (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ s) (hρ₀_eq : ρ₀ = (β : ℂ) + (γ : ℂ) * I) (hmρ₀ : m ρ₀ = k)
    (hother : ∀ ρ ∈ s, ρ ≠ ρ₀ → ρ.re < σ) :
    (k : ℝ) / (σ - β)
      ≤ (∑ ρ ∈ s, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * I) - ρ)).re := by sorry
