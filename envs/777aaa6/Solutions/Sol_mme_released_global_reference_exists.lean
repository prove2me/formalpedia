-- Prove2me | solution 1 for mme_released_global_reference_exists
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T23:26:41.424993+00:00
-- url     : https://prove2.me/submissions/de6001dd-f554-49e6-8b7c-2563c418fac1

import Theorems.Thm_mme_regional_reference_exists_iff_mass
import Definitions.Def_mme_released_global_frame_data

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false

-- Each released owner's coarse weights have exactly the prescribed total mass.
private theorem sum_alpha : ∀ owner : Fin 6, ∑ s : Fin 45, alpha owner s = denominator := by
  decide +kernel

private theorem sum_coarse (owner : Fin 6) :
    ∑ c : Shape, coarseCounts owner c = denominator ^ 5 := by
  classical
  rw [← Equiv.sum_comp shapeEquiv]
  simp only [coarseCounts, Equiv.symm_apply_apply]
  rw [← Finset.sum_mul, sum_alpha]
  ring

theorem solution (owner : Fin 6) (k : ℕ) :
    Nonempty (Reference owner k) := by
  classical
  obtain ⟨a, ha⟩ := (mme_regional_reference_exists_iff_mass (counts owner k)).mpr (by
    intro r
    change (∑ c : Shape, k * coarseCounts owner c) = blocks k
    rw [← Finset.mul_sum, sum_coarse]
    unfold blocks
    exact Nat.mul_comm k (denominator ^ 5))
  exact ⟨⟨a, ha⟩⟩

#print axioms solution
