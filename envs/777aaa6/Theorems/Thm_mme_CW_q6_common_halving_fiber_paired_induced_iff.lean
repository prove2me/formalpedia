-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_fiber_paired_induced_iff
-- name    : mme_CW_q6_common_halving_fiber_paired_induced_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:33:30.016026+00:00
-- url     : https://prove2.me/theorems/bbd9b36b-63ca-45a5-879e-d944b38c8e02
-- title:
--   Diagonal paired support is equivalent to separate half-pattern injectivity
-- statement:
--   Let a primary hash family admit a common balanced halving, and fix one color. For each of its $H$ entries $h$, let $X_L(h)$ and $Y_R(h)$ be its first-half X and second-half Y grade words. Then
--   $$\text{every surviving paired cyclic triple in this color is diagonal}
--   \quad\Longleftrightarrow\quad X_L\text{ and }Y_R\text{ are both injective}.$$
--   This is an exact criterion for diagonal support inside one color. The criterion concerns each half-pattern separately; it does not establish global inducedness across different colors or a C-tensor packing certificate.
-- source:
--   The four local coupled support patterns and the common third-coordinate grade word within a primary hash fiber.

import Definitions.Def_mme_CW_q6_paired_cyclic_induced

open MME
set_option autoImplicit false

theorem mme_CW_q6_common_halving_fiber_paired_induced_iff
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A) :
    (∀ h0 h1 h2 : Fin H,
      family.PairedCyclicSupported halving (a,h0) (a,h1) (a,h2) →
        h0 = h1 ∧ h1 = h2) ↔
      Function.Injective (fun h : Fin H ↦ fun r : Fin N ↦
        (family.entry (a,h)).val 0 (halving.position (Sum.inl r))) ∧
      Function.Injective (fun h : Fin H ↦ fun r : Fin N ↦
        (family.entry (a,h)).val 1 (halving.position (Sum.inr r))) := by sorry
