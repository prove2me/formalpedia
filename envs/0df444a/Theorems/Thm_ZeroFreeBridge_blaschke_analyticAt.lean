-- Prove2me | Theorems.Thm_ZeroFreeBridge_blaschke_analyticAt
-- name    : ZeroFreeBridge.blaschke_analyticAt
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:38.118247+00:00
-- url     : https://prove2.me/theorems/35b47775-a8e2-4dcb-b000-d9c2e65f41c6
-- title:
--   Analyticity of a finite canonical product
-- statement:
--   Let $n:\mathbb C\to\mathbb Z$ have finite support $S\subset B(0,R)$. If
--   $z\in\overline{B(0,R)}$ and $z\notin S$, then the finite product of defined
--   canonical factors
--   $$z\longmapsto\prod_{u\in S}F_{R,u}(z)^{n(u)}$$
--   is analytic at $z$. The exclusion permits negative integer exponents.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBlaschkeProdAnalytic.lean#L20-L40

import Mathlib
/- PHASE 4 (dVP frontier, BLASCHKE item (d2) sub-lemma): the finite Blaschke product is analytic
   AWAY FROM ITS ZEROS.

   The Blaschke product `∏ᶠ_u (canonicalFactor R u)^{n u}` has (for `n = -divisor ≤ 0`) removable
   singularities exactly at the support points `u`.  AT a point `z` avoiding all of them, each factor
   is genuinely analytic and nonzero (`canonicalFactor` is analytic off `{u}` and nonzero away from
   `u` inside the disk), so `AnalyticAt.zpow` applies to each and `Finset.analyticAt_prod` to the
   product — NO meromorphic-order argument needed.

   This is exactly the analyticity the codiscrete → pointwise transfer (`DlvpTransfer`) needs to split
   `logDeriv ζ = logDeriv(Blaschke) + logDeriv g` at points off the zeros (item d2).  Function-agnostic
   in the exponent `n`.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.blaschke_analyticAt {R : ℝ} (n : ℂ → ℤ) (hn : (Function.support n).Finite)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R)
    (hsupp : ∀ u ∈ hn.toFinset, u ∈ ball (0 : ℂ) R)
    (hzne : ∀ u ∈ hn.toFinset, z ≠ u) :
    AnalyticAt ℂ (∏ᶠ u, (canonicalFactor R u) ^ (n u)) z := by sorry
