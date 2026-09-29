-- Prove2me | solution 1 for mme_integer_regional_entropy_copy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:18:53.261985+00:00
-- url     : https://prove2.me/submissions/224118ee-fd0e-4485-8bad-4bb298e03d3c

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_integer_regional_common_scale_entropy_bound
import Theorems.Thm_mme_regional_target_entropy_bounds
import Theorems.Thm_mme_entropy_retention_lower_bound
import Mathlib
open BigOperators MME MME.RegionRate MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution {ell M : ℕ} {P : ProfiledCW.Predicate M} (D : IntegerStep ell M P) :
    D.entropyLower ≤ D.lower ∧ D.entropyCopies ≤ D.copies := by
  have hs := mme_integer_regional_common_scale_entropy_bound D
  have ht := (mme_regional_target_entropy_bounds D.m 0 D.reference D.reference_target).2.1
  have hQ : 0 < D.scale := by
    unfold IntegerStep.scale commonScale
    exact (Nat.succ_pos D.half).trans_le (le_max_left _ _)
  have hp : 0 < polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)) := by
    unfold polynomialFactor
    positivity
  have hf : 0 < scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell := by
    unfold scaleFactor loadFactor polynomialFactor ambientFactor
    positivity
  have h := mme_entropy_retention_lower_bound
    ((RecursiveXHash.target (n := D.n) D.m).card : ℝ) (D.scale : ℝ) (jointPotential D.m)
    (scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell)
    (scaleExponent D.total D.n D.m D.mu D.epsilon)
    (polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)))
    (Nat.cast_nonneg _) (by exact_mod_cast hQ) hf hp ht hs.2
  have he : jointPotential D.m - scaleExponent D.total D.n D.m D.mu D.epsilon =
      regionalRate D.total D.n D.m D.mu - ((∑ r, D.n r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) D.epsilon := by
    unfold scaleExponent
    ring
  rw [he] at h
  have hbound : D.entropyLower ≤ D.lower := h
  refine ⟨hbound,?_⟩
  unfold IntegerStep.entropyCopies IntegerStep.copies
  exact Nat.div_le_div_right (Nat.floor_mono hbound)
