-- Prove2me | Theorems.Thm_ZeroFreeBridge_logDeriv_finprod_canonicalFactor
-- name    : ZeroFreeBridge.logDeriv_finprod_canonicalFactor
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:44:55.067882+00:00
-- url     : https://prove2.me/theorems/8ac81000-71af-46c2-bebb-00ac6f1ca588
-- title:
--   Logarithmic derivative of a canonical product
-- statement:
--   Let $n:\mathbb C\to\mathbb Z$ have finite support $S$, and let every defined
--   factor $F_{R,u}$, $u\in S$, be differentiable and nonzero at $z$. Then
--   $$\operatorname{logDeriv}\left(\prod_{u\in S}F_{R,u}^{n(u)}\right)(z)
--   =\sum_{u\in S}n(u)\operatorname{logDeriv}F_{R,u}(z).$$
--   This separates the contributions of individual canonical factors.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBlaschkeHerglotz.lean#L20-L46

import Mathlib
/- PHASE 4 (dVP frontier, BLASCHKE item (d1)): the log-derivative of the finite Blaschke product
   is the sum of the canonical-factor log-derivatives.

   Mirrors the monomial `DlvpHerglotz.logDeriv_prod_sub_zpow`, but with `canonicalFactor` in place of
   `(·-ρ)`.  For a finitely-supported integer exponent `n`, at a point `z` where each factor is
   differentiable and nonzero,

     `logDeriv (∏ᶠ_u (canonicalFactor R u)^{n u}) z = Σ_u (n u)·logDeriv (canonicalFactor R u) z`.

   Combined with `DlvpCanonicalLogDeriv.logDeriv_canonicalFactor`, each term expands to the Herglotz
   contribution `−(n u)/(z-u)` plus the bounded correction `−(n u)·conj u/(R²-conj u·z)`.  This is the
   Blaschke analog of the obligation-(i) Herglotz sum.  Function-agnostic.  conjecture1_proved = False.
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.logDeriv_finprod_canonicalFactor {R : ℝ} (n : ℂ → ℤ)
    (hn : (Function.support n).Finite) (z : ℂ)
    (hdiff : ∀ u ∈ hn.toFinset, DifferentiableAt ℂ (canonicalFactor R u) z)
    (hne : ∀ u ∈ hn.toFinset, canonicalFactor R u z ≠ 0) :
    logDeriv (∏ᶠ u, (canonicalFactor R u) ^ (n u)) z
      = ∑ u ∈ hn.toFinset, (n u : ℂ) * logDeriv (canonicalFactor R u) z := by sorry
