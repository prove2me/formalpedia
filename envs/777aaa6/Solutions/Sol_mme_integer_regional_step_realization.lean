-- Prove2me | solution 1 for mme_integer_regional_step_realization
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:35:18.196476+00:00
-- url     : https://prove2.me/submissions/0c2a8c40-0537-4d3d-b2f5-9c7967c87313

import Definitions.Def_mme_integer_regional_CW_recipe
import Theorems.Thm_mme_recursive_region_actual_exact_step_realization

open BigOperators MME MME.ProfiledCW MME.RegionRealization MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem enlarge_source {ell N : ℕ} {P Q : Predicate N}
    (E : ExactStep ell N P) (hPQ : ∀ i x, P i x → Q i x) :
    ∃ F : ExactStep ell N Q, F.copies = E.copies ∧ F.output = E.output := by
  classical
  let F : ExactStep ell N Q := {
    hash := E.hash
    stage := E.stage
    level := E.level
    length := E.length
    count := E.count
    state := E.state
    address := E.address
    injective := E.injective
    target := E.target
    bucketed := E.bucketed
    hashed := E.hashed
    isolated := E.isolated
    holes := by
      intro j i
      apply le_trans _ (E.holes j i)
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      apply Finset.union_subset_union
      · intro f hf
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1,
          fun h ↦ (Finset.mem_filter.mp hf).2 (hPQ i _ h)⟩
      · exact Finset.Subset.refl _ }
  exact ⟨F,rfl,rfl⟩

theorem solution {ell N : ℕ} {P : Predicate N} (D : IntegerStep ell N P) :
    ∃ E : ExactStep ell N P, D.copies ≤ E.copies ∧ E.output = D.output := by
  classical
  obtain ⟨E,hcount,hexp,hout⟩ := mme_recursive_region_actual_exact_step_realization D.parent D.n
    D.total D.half_eq D.m D.hashPositions D.positions D.length D.mu D.mass D.support D.boundary
    D.reference D.reference_target D.minimum D.repairScale D.minimum_pos D.repairScale_gt_one
    D.parent_size D.split_divisible D.epsilon D.epsilon_pos D.size_test
  have hc : D.lower ≤ (E.count : ℝ) := hcount
  have he : E.stage.repairExponent = D.repairExponent := hexp
  have hcopies : D.copies ≤ E.copies := by
    change ⌊D.lower⌋₊ / 8 ^ D.repairExponent ≤ E.count / 8 ^ E.stage.repairExponent
    rw [he]
    exact Nat.div_le_div_right (Nat.floor_le_of_le hc)
  obtain ⟨F,hFc,hFo⟩ := enlarge_source E D.source_inside
  exact ⟨F, hcopies.trans_eq hFc.symm, hFo.trans hout⟩
