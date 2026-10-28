-- Prove2me | Theorems.Thm_ZeroFreeBridge_logDeriv_split_off_zeros
-- name    : ZeroFreeBridge.logDeriv_split_off_zeros
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:55:51.332976+00:00
-- url     : https://prove2.me/theorems/8e62e6a9-d7f8-4937-a8c0-00756acf6768
-- title:
--   Splitting the logarithmic derivative at the zeros
-- statement:
--   Suppose $f$ and $g$ have the defined canonical decomposition on $B(0,R)$, both
--   are analytic near the disk, and $g$ is zero-free there. Let $S$ be the finite
--   support of $-\operatorname{div}(f)$ in the disk, and let $z$ lie in the disk but
--   outside $S$. Then, for the defined canonical factors $F_{R,u}$,
--   $$\operatorname{logDeriv}f(z)=\sum_{u\in S}
--   (-\operatorname{div}(f)(u))\operatorname{logDeriv}F_{R,u}(z)
--   +\operatorname{logDeriv}g(z).$$
--   This separates the divisor terms from the zero-free factor.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpBlaschkeSplit.lean#L25-L95

import Mathlib
import Theorems.Thm_ZeroFreeBridge_blaschke_analyticAt
import Theorems.Thm_ZeroFreeBridge_logDeriv_finprod_canonicalFactor
/- PHASE 4 (dVP frontier, BLASCHKE item (d2)): the log-derivative split for the canonical
   decomposition — `logDeriv ζ = Σ (canonical-factor log-derivatives) + logDeriv g`.

   Off the zeros, the codiscrete factorization `f =ᶠ (∏ᶠ canonicalFactor^{-divisor}) • g` upgrades to
   a pointwise log-derivative identity: work on a small CONVEX ball `B(z,ε) ⊆ ball 0 R` that avoids
   the finitely many zeros (extracted from the OPEN set `ball 0 R \ zeros`), where both `f` and the
   Blaschke·g product are analytic (`DlvpBlaschkeProdAnalytic.blaschke_analyticAt` for the Blaschke
   part), then apply the function-agnostic transfer `DlvpTransfer.logDeriv_congr_of_codiscrete`,
   `logDeriv_mul`, and the Blaschke Herglotz sum `DlvpBlaschkeHerglotz.logDeriv_finprod_canonicalFactor`.

     `logDeriv_split_off_zeros` :  for a `CanonicalDecomp f g R` with `f, g` analytic and `g` zero-free,
       at `z ∈ ball 0 R` off the zeros,
         `logDeriv f z = Σ_u (-divisor f (ball 0 R) u)·logDeriv (canonicalFactor R u) z + logDeriv g z`.

   conjecture1_proved = False (NOT a proof of RH).
-/




open Complex Metric MeromorphicOn Filter

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.logDeriv_split_off_zeros {f g : ℂ → ℂ} {R : ℝ}
    (D : CanonicalDecomp f g R)
    (hf_ana : AnalyticOnNhd ℂ f (ball 0 R)) (hg_ana : AnalyticOnNhd ℂ g (ball 0 R))
    (hg_ne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0)
    (hfin : (Function.support (fun u => -(divisor f (ball 0 R) u))).Finite)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hzne : ∀ u ∈ hfin.toFinset, z ≠ u) :
    logDeriv f z
      = (∑ u ∈ hfin.toFinset,
          ((-(divisor f (ball 0 R) u) : ℤ) : ℂ) * logDeriv (canonicalFactor R u) z)
        + logDeriv g z := by sorry
