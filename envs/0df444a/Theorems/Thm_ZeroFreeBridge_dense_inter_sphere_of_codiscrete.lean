-- Prove2me | Theorems.Thm_ZeroFreeBridge_dense_inter_sphere_of_codiscrete
-- name    : ZeroFreeBridge.dense_inter_sphere_of_codiscrete
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:43:37.985462+00:00
-- url     : https://prove2.me/theorems/e328e98d-09ae-4203-b620-3a94c34cb520
-- title:
--   Codiscrete sets meet a dense part of a circle
-- statement:
--   Let $R>0$, and let $A\subset\mathbb C$ belong to the codiscrete filter within
--   the closed disk $\overline{B(0,R)}$. Then
--   $$\{z:|z|=R\}\subseteq\overline{A\cap\{z:|z|=R\}}.$$
--   This extends identities known off a discrete exceptional set to the full circle.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/DlvpSphereDense.lean#L20-L61

import Mathlib
/- PHASE 4 (dVP frontier, BLASCHKE step 1 — DENSITY DISCHARGE): a codiscrete subset of the closed
   ball is dense within the boundary sphere.

   `DlvpBlaschkeSphere.norm_eq_of_codiscrete_factor_on_sphere` isolated one hypothesis: the
   agreement set of the codiscrete factorization is DENSE in `sphere 0 R`.  This file discharges it.

   The sphere is CONNECTED (`isConnected_sphere`, since `ℂ` has real rank 2) and nontrivial
   (`R > 0`), hence PREPERFECT (`IsPreconnected.preperfect_of_nontrivial`): every sphere point is an
   accumulation point of the sphere.  A codiscrete set `A` on `closedBall` satisfies `A ∪ (closedBall)ᶜ
   ∈ 𝓝[≠] z`; restricted to the punctured sphere (⊆ `closedBall`), this means `A` holds on the
   accumulating punctured-sphere filter — so every sphere point is a cluster point of `A ∩ sphere`,
   i.e. `sphere ⊆ closure (A ∩ sphere)`.  Function-agnostic.  conjecture1_proved = False (NOT RH).
-/


open Complex Metric Filter Topology Set

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge

theorem ZeroFreeBridge.dense_inter_sphere_of_codiscrete {A : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hA : A ∈ codiscreteWithin (closedBall (0 : ℂ) R)) :
    sphere (0 : ℂ) R ⊆ closure (A ∩ sphere 0 R) := by sorry
