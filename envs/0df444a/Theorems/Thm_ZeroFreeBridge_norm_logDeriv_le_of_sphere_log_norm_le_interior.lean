-- Prove2me | Theorems.Thm_ZeroFreeBridge_norm_logDeriv_le_of_sphere_log_norm_le_interior
-- name    : ZeroFreeBridge.norm_logDeriv_le_of_sphere_log_norm_le_interior
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:58.88231+00:00
-- url     : https://prove2.me/theorems/e1da5215-275f-4c91-9850-144140a706a1
-- title:
--   Interior logarithmic-derivative bound from the boundary
-- statement:
--   Let $g$ be holomorphic in $B(c,R)$ and continuous on its closure, with no zero in
--   the open disk. Suppose $M>0$, $|z_0-c|<R$, and
--   $\log|g(z)|-\log|g(c)|\le M$ for $|z-c|=R$. Writing $\rho=|z_0-c|$,
--   $$|g'(z_0)/g(z_0)|\le\frac{4M(R+\rho)}{(R-\rho)^2}.$$
--   The boundary oscillation therefore controls the interior logarithmic derivative.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpEntirePlumbing.lean#L24-L50

import Mathlib
import Theorems.Thm_ZeroFreeBridge_norm_logDeriv_le_of_log_norm_le_interior
/- PHASE 4 (dVP frontier, entire-part PLUMBING): the two mechanical lemmas that connect the
   interior-point bound (`DlvpBCDerivInterior`) to the Blaschke BC-SUM (`bc_sum_blaschke`).

   (a) `norm_logDeriv_le_of_sphere_log_norm_le_interior` — the interior entire-part bound driven by a
       SPHERE oscillation bound (not the whole ball): `log‖g‖ = Re(log g)` is harmonic, so a boundary
       bound propagates to the disk by maximum modulus (`DlvpMaxMod.norm_le_on_ball_of_sphere`, via
       `exp`), and the resulting ball bound feeds `norm_logDeriv_le_of_log_norm_le_interior`.  This is
       exactly the shape available for ζ's Blaschke `g`, whose boundary `log‖g‖` equals `log‖ζ‖`
       (Blaschke factors have modulus 1 on the sphere).

   (b) `logDeriv_comp_const_add` — the RECENTRING: `bc_sum_blaschke` lives on `ball 0 R`, so ζ enters as
       `f(w) = ζ(c + w)`; its log-derivative is ζ's, shifted: `logDeriv (fun w => ζ(c+w)) z =
       logDeriv ζ (c+z)` (chain rule, `deriv (c+·) = 1`).

   conjecture1_proved = False (NOT a proof of RH).
-/



open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.norm_logDeriv_le_of_sphere_log_norm_le_interior {g : ℂ → ℂ} {c z₀ : ℂ} {R M' : ℝ}
    (hM' : 0 < M') (hρ : ‖z₀ - c‖ < R)
    (hd : DiffContOnCl ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hsphere : ∀ z ∈ sphere c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g z₀‖ ≤ 4 * M' * (R + ‖z₀ - c‖) / (R - ‖z₀ - c‖) ^ 2 := by sorry
