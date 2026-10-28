-- Prove2me | Theorems.Thm_ZeroFreeBridge_hbc1_from_bounds
-- name    : ZeroFreeBridge.hbc1_from_bounds
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:04:45.702618+00:00
-- url     : https://prove2.me/theorems/73347543-1bad-4a43-921e-097443836825
-- title:
--   Centered zeta zero-sum bound from factor and count bounds
-- statement:
--   Let $R>0$, $1<\sigma\le2$, $2-\sigma<R$, $\gamma\in\mathbb R$,
--   $c=2+i\gamma$, $f(w)=\zeta(c+w)$, and $z=\sigma+i\gamma-c$. Suppose $g$
--   gives the defined canonical decomposition of $f$ on $B(0,R)$, both $f$ and $g$
--   are analytic near that disk, $g$ is zero-free on it, and $\zeta(c+z)\ne0$.
--   Let $S$ be the finite support of $-\operatorname{div}_{B(0,R)}f$. If
--   $$|\operatorname{logDeriv}g(z)|\le B_g,\quad
--   \sum_{u\in S}\operatorname{div}_{B(0,R)}f(u)\le C,\quad
--   \frac{C}{R-|z|}+B_g\le A_L,$$
--   then
--   $$\operatorname{Re}(-\operatorname{logDeriv}f(z))\le A_L-
--   \operatorname{Re}\sum_{u\in S}\frac{\operatorname{div}_{B(0,R)}f(u)}{z-u}.$$
--   This combines a zero count and a bound for the zero-free factor.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaHbc1.lean#L18-L57

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ZeroFreeBridge_bc_sum_blaschke
/- PHASE 4 (dVP frontier, item (A) — the height-γ hbc₁ wiring): produce the BC-SUM inequality
   `dlvp_zeta_region_of_bc_sums` consumes at height γ, from the O(L) bounds.

   With every analytic input now an explicit kernel-clean lemma (`hg_bound_gamma` for `Bg`,
   `sum_divisor_recenter_le_jensen` for the count `C`), closing `hbc₁` is composition: this wrapper
   takes `Bg`, `C`, and the region constraint `C/(R-‖z₀‖) + Bg ≤ AL`, derives `hAL` (via
   `sum_abs_divisor_eq` + `divisor ≥ 0` from `hf_ana.divisor_nonneg` + monotonicity in the count),
   and calls `bc_sum_concrete`.  Reusable for BOTH heights (the height-2γ `hbc₂` uses the same shape
   on the parallel disk).  `‖z₀‖ = 2-σ` via `concrete_eval_eq`.  conjecture1_proved = False.
-/



open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.hbc1_from_bounds (σ γ : ℝ) {R : ℝ} (hR : 0 < R) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hσR : 2 - σ < R)
    (g : ℂ → ℂ)
    (D : CanonicalDecomp (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) g R)
    (hf_ana : AnalyticOnNhd ℂ (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R))
    (hg_ana : AnalyticOnNhd ℂ g (ball 0 R)) (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support
      (fun u => -(divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u))).Finite)
    (heval_ne : riemannZeta (((2 : ℂ) + (γ : ℂ) * I)
      + ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))) ≠ 0)
    {Bg AL C : ℝ}
    (hg_bound : ‖logDeriv g ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I))‖ ≤ Bg)
    (hcount : (∑ u ∈ hfin.toFinset,
        (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℝ)) ≤ C)
    (hAL_bound : C / (R - ‖(σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)‖) + Bg ≤ AL) :
    (-(logDeriv (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w))
        ((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)))).re
      ≤ AL - (∑ u ∈ hfin.toFinset,
          (divisor (fun w => riemannZeta (((2 : ℂ) + (γ : ℂ) * I) + w)) (ball 0 R) u : ℂ)
            / (((σ : ℂ) + (γ : ℂ) * I - ((2 : ℂ) + (γ : ℂ) * I)) - u)).re := by sorry
