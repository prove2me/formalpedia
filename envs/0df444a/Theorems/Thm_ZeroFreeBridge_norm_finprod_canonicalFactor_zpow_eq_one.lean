-- Prove2me | Theorems.Thm_ZeroFreeBridge_norm_finprod_canonicalFactor_zpow_eq_one
-- name    : ZeroFreeBridge.norm_finprod_canonicalFactor_zpow_eq_one
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:29.770284+00:00
-- url     : https://prove2.me/theorems/cbd12fe4-03ab-4ee7-9a0b-1071684e588d
-- title:
--   Boundary modulus of a finite canonical product
-- statement:
--   Let $n:\mathbb C\to\mathbb Z$ have finite support $S\subset B(0,R)$, and let
--   $F_{R,u}$ be the defined canonical factor. For every $|z|=R$,
--   $$\left|\prod_{u\in S}F_{R,u}(z)^{n(u)}\right|=1.$$
--   The product has unit modulus on the boundary circle.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBlaschke.lean#L24-L47

import Mathlib
/- PHASE 4 (dVP frontier, BLASCHKE correction): the finite Blaschke product has modulus 1 on the
   sphere — the fact that removes the lossy AP term.

   The monomial factorization `ζ = ∏(·-ρ)^m · g` fails to give `M' = O(L)`: near a boundary zero the
   decomposition `log‖g‖ = log‖ζ‖ - log‖P‖` throws away a cancellation, so `AP` blows up.  The
   classical fix uses BLASCHKE factors, and Mathlib already has them:
   `canonicalFactor R w z = (R² - conj w · z)/(R(z-w))` (`Analysis/Complex/CanonicalDecomposition`),
   with `‖canonicalFactor R w z‖ = 1` for `z ∈ sphere 0 R`, `w ∈ ball 0 R`
   (`norm_canonicalFactor_eval_circle_eq_one`), and the full decomposition `MeromorphicOn.exists_
   canonicalDecomp`: `f =ᶠ (∏ᶠ_u canonicalFactor^{-divisor u}) • g` with `g` zero-free on the ball.

   This file lifts the single-factor modulus-1 fact to the whole finite product: for a finitely
   supported exponent `n` with support in `ball 0 R`,
     `‖(∏ᶠ_u (canonicalFactor R u)^{n u}) z‖ = 1`   for   `z ∈ sphere 0 R`.
   Consequently `‖f‖ = ‖g‖` on the sphere (up to the codiscrete exceptional set) — so the boundary
   `M'` is `sup log‖f‖ - log‖g c‖ = O(L)` with NO zero-factor term.  conjecture1_proved = False.
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.norm_finprod_canonicalFactor_zpow_eq_one {R : ℝ} (n : ℂ → ℤ)
    (hn : (Function.support n).Finite)
    (hsupp : ∀ u ∈ hn.toFinset, u ∈ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) R) :
    ‖(∏ᶠ u, (canonicalFactor R u) ^ (n u)) z‖ = 1 := by sorry
