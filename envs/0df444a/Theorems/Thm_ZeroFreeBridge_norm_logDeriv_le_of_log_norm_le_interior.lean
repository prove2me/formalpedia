-- Prove2me | Theorems.Thm_ZeroFreeBridge_norm_logDeriv_le_of_log_norm_le_interior
-- name    : ZeroFreeBridge.norm_logDeriv_le_of_log_norm_le_interior
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:55.582177+00:00
-- url     : https://prove2.me/theorems/e46b601f-53e0-4046-97cf-3a2754f81257
-- title:
--   Interior logarithmic-derivative bound
-- statement:
--   Let $g$ be holomorphic and zero-free in the disk $B(c,R)$, let $z_0$ lie in that
--   disk, and suppose $M>0$ and $\log|g(z)|-\log|g(c)|\le M$ throughout the disk.
--   Writing $\rho=|z_0-c|$, one has
--   $$|g'(z_0)/g(z_0)|\le\frac{4M(R+\rho)}{(R-\rho)^2}.$$
--   This controls the zero-free factor at an interior point.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBCDerivInterior.lean#L23-L102

import Mathlib
import Theorems.Thm_ZeroFreeBridge_log_branch_of_analytic_nonvanishing
/- PHASE 4 (dVP frontier, the CENTRE→EVALUATION-POINT transfer — item 3, the sole remaining hard core):
   bound the entire part `logDeriv g` at an INTERIOR point `z₀`, not just the centre.

   `DlvpBCDeriv.norm_deriv_le_of_re_le` bounds `‖logDeriv g c‖` at the disk CENTRE.  The dVP BC-SUM
   (`bc_sum_blaschke`) needs `‖logDeriv g z₀‖` at the EVALUATION point `z₀` (off-centre, `Re ≈ 1`).
   Borel–Carathéodory turns the one-sided oscillation bound `log‖g w‖ - log‖g c‖ ≤ M'` on `ball c R`
   into a TWO-sided value bound `‖h w - h c‖ ≤ 2M'‖w-c‖/(R-‖w-c‖)` (`h = log g`, `Re h = log‖g‖`), for
   EVERY interior `w` — not just on one sphere.  A Cauchy estimate on the sphere `‖w - z₀‖ = (R-ρ)/2`
   (`ρ = ‖z₀-c‖`), which lies inside `ball c R`, then bounds the derivative at `z₀`:

     `‖logDeriv g z₀‖ ≤ 4 M' (R + ρ) / (R - ρ)²`.

   The `2M'‖w‖/(R-‖w‖)` value bound is increasing in `‖w‖`, so on that sphere it is `≤ 2M'(R+ρ)/(R-ρ)`;
   dividing by the Cauchy radius `(R-ρ)/2` gives the stated constant.  With `M' = O(L)` and `ρ, R = O(1)`
   this is `O(L)` — exactly `bc_sum_blaschke`'s `Bg`.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.norm_logDeriv_le_of_log_norm_le_interior {g : ℂ → ℂ} {c z₀ : ℂ} {R M' : ℝ}
    (hM' : 0 < M') (hρ : ‖z₀ - c‖ < R)
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hbound : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g z₀‖ ≤ 4 * M' * (R + ‖z₀ - c‖) / (R - ‖z₀ - c‖) ^ 2 := by sorry
