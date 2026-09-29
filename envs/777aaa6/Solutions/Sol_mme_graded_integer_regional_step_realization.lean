-- Prove2me | solution 1 for mme_graded_integer_regional_step_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T15:47:40.423977+00:00
-- url     : https://prove2.me/submissions/6b184769-046b-4939-a4ac-24b59ea0559e

import Definitions.Def_mme_graded_integer_regional_step_data
import Theorems.Thm_mme_recursive_region_exact_step_realization_graded

open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private theorem split_flatten' {S : Type} {ell L M : ℕ} (positions : Fin L ≃ S)
    (length : L * 2 ^ (ell - 1) = M) (f : S → CompleteSplit.CompleteWord ell) :
    ProfiledCW.split positions length (ProfiledCW.flatten positions length f) = f := by
  funext p h
  simp [ProfiledCW.split, ProfiledCW.flatten]


theorem solution {ell M : ℕ} {P : ProfiledCW.Predicate M} (D : IntegerStepG ell M P) :
    ∃ E : ExactStep ell M P, D.step.copies ≤ E.copies ∧ E.output = D.step.output := by
  classical
  obtain ⟨E, hcount, hexp, hout⟩ := mme_recursive_region_exact_step_realization_graded D.step.parent D.step.n
    D.step.total D.step.half_eq D.step.m D.step.hashPositions D.step.positions D.step.length
    D.step.mu D.step.mass D.step.support D.step.boundary D.step.reference D.step.reference_target
    D.step.minimum D.step.repairScale D.step.minimum_pos D.step.repairScale_gt_one
    D.step.parent_size D.step.split_divisible D.step.epsilon D.step.epsilon_pos D.step.size_test P
    (fun i f hgr ht ↦ D.graded_inside i _ (by rwa [split_flatten'])
      (D.step.source_inside i _ (by rwa [split_flatten'])))
  have hc : D.step.lower ≤ (E.count : ℝ) := hcount
  have he : E.stage.repairExponent = D.step.repairExponent := hexp
  refine ⟨E, ?_, hout⟩
  change ⌊D.step.lower⌋₊ / 8 ^ D.step.repairExponent ≤ E.count / 8 ^ E.stage.repairExponent
  rw [he]
  exact Nat.div_le_div_right (Nat.floor_le_of_le hc)

