-- Prove2me | Theorems.Thm_ZeroFreeBridge_zeta_center_factorization
-- name    : ZeroFreeBridge.zeta_center_factorization
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:53:49.895056+00:00
-- url     : https://prove2.me/theorems/6a7bcdda-2b10-4341-a20a-a966b22d5294
-- title:
--   Canonical factorization at the disk center
-- statement:
--   Let $c\in\mathbb C$, $R>0$, and let the defined canonical decomposition relate
--   $f(w)=\zeta(c+w)$ and $g$ on $B(0,R)$. Suppose both $f$ and $Bg$ are continuous
--   at zero, where
--   $$B(w)=\prod{}^{\!f}_{u}F_{R,u}(w)^{-\operatorname{div}(f)(u)}$$
--   is the finite-support product of defined canonical factors and the divisor is
--   taken in $B(0,R)$. Then
--   $$\zeta(c)=B(0)g(0).$$
--   This extends the canonical factorization to the disk center.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpZetaCentreFac.lean#L18-L46

import Mathlib
/- PHASE 4 (dVP frontier, hfac0 — the centre factorization ζ c₀ = B 0 · g 0): the codiscrete→pointwise
   step, the last piece of analysis in item 2.

   The CanonicalDecomp gives `f = B·g` CODISCRETELY (`D.eventuallyEq`), `f = ζ(c₀+·)`.  At the centre `0`
   (where `f 0 = ζ c₀ ≠ 0`, so `0` is not a zero and `B` is analytic), the identity principle upgrades
   this to the POINTWISE `ζ c₀ = B 0 · g 0`: codiscrete membership gives frequent agreement in `𝓝[≠] 0`
   (`mem_codiscreteWithin_iff_forall_mem_nhdsNE`), and both sides continuous at `0` (`f` analytic; `B·g`
   the finite Blaschke product times the analytic `g`) pins the values equal (`tendsto_nhds_unique`,
   `𝓝[≠] 0` NeBot on ℂ).  The continuities are taken as hypotheses (`f` is entire-shifted; `B·g` is
   continuous at `0` since `0` is not among the finitely many zeros).  conjecture1_proved = False.
-/


open Complex MeromorphicOn Metric Filter Topology

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.zeta_center_factorization {c₀ : ℂ} {R : ℝ} {g : ℂ → ℂ} (hR : 0 < R)
    (D : CanonicalDecomp (fun w => riemannZeta (c₀ + w)) g R)
    (hf_cont0 : ContinuousAt (fun w => riemannZeta (c₀ + w)) 0)
    (hBg_cont0 : ContinuousAt
      ((∏ᶠ u, (canonicalFactor R u) ^ (-divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u)) • g) 0) :
    riemannZeta c₀
      = (∏ᶠ u, (canonicalFactor R u) ^ (-divisor (fun w => riemannZeta (c₀ + w)) (ball 0 R) u)) 0
        * g 0 := by sorry
