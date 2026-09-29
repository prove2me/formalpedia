-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_fiber_paired_support_iff
-- name    : mme_CW_q6_common_halving_fiber_paired_support_iff
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:33:29.561884+00:00
-- url     : https://prove2.me/theorems/57904f48-be3f-4bc6-b9dc-c1b8a5e62c7e
-- title:
--   Exact paired support within one common-halving color
-- statement:
--   Let a primary hash family admit a common balanced halving into two sets of $N$ positions. Fix a color with $H$ entries, and write $X_L(h)$ for the first-half X grade word and $Y_R(h)$ for the second-half Y grade word of entry $h$. For any three entries $h_0,h_1,h_2$ in this color, the paired cyclic mixed choice survives exactly when
--   $$X_L(h_0)=X_L(h_2)\quad\text{and}\quad Y_R(h_1)=Y_R(h_2).$$
--   This describes the surviving mixed terms using the two half-patterns. It applies to every color, including colors whose common Z word contains both pure and mixed positions.
-- source:
--   The four local coupled support patterns and the common third-coordinate grade word within a primary hash fiber.

import Definitions.Def_mme_CW_q6_paired_cyclic_induced

open MME
set_option autoImplicit false

theorem mme_CW_q6_common_halving_fiber_paired_support_iff
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A)
    (h0 h1 h2 : Fin H) :
    family.PairedCyclicSupported halving (a,h0) (a,h1) (a,h2) ↔
      (∀ r : Fin N, (family.entry (a,h0)).val 0 (halving.position (Sum.inl r)) =
        (family.entry (a,h2)).val 0 (halving.position (Sum.inl r))) ∧
      (∀ r : Fin N, (family.entry (a,h1)).val 1 (halving.position (Sum.inr r)) =
        (family.entry (a,h2)).val 1 (halving.position (Sum.inr r))) := by sorry
