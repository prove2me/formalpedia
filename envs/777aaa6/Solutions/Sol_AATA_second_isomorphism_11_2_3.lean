-- Prove2me | solution 1 for AATA.second_isomorphism_11_2_3
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:10:08.411841+00:00
-- url     : https://prove2.me/submissions/7e55fa52-caf0-40ba-bf0c-34b094e6d9b4

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u v

theorem solution {G : Type u} [Group G] (K N : Subgroup G) [N.Normal] :
    ((K ⊔ N : Subgroup G) : Set G) =
      {g : G | ∃ k ∈ K, ∃ n ∈ N, k*n = g} ∧
    (N.subgroupOf K).Normal ∧
    Nonempty (K ⧸ N.subgroupOf K ≃*
      (K ⊔ N : Subgroup G) ⧸ N.subgroupOf (K ⊔ N)) := by
  refine ⟨?_, inferInstance, ⟨QuotientGroup.quotientInfEquivProdNormalQuotient K N⟩⟩
  exact Subgroup.coe_mul_of_left_le_normalizer_right K N Subgroup.le_normalizer_of_normal
