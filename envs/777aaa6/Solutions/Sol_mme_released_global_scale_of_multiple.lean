-- Prove2me | solution 1 for mme_released_global_scale_of_multiple
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T03:18:12.981078+00:00
-- url     : https://prove2.me/submissions/5375a666-146e-48b9-a5c9-7d9d1bee0940

import Definitions.Def_mme_released_global_frame_data
open MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false

/-- A parent replication divisible by the released coarse weight yields a
positive global replication with exactly the same number of coarse blocks. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hpos : 0 < alpha owner s)
    (K k : ℕ) (hk : 0 < k) (hdiv : alpha owner s ∣ k)
    (hK : alpha owner s * K ≤ k) :
    ∃ t : ℕ, K ≤ t ∧ 0 < t ∧ k = alpha owner s * t ∧
      t * coarseCounts owner (shapeEquiv s) = k * denominator^4 := by
  obtain ⟨t, ht⟩ := hdiv
  have htpos : 0 < t := by
    by_contra hn
    have : t = 0 := by omega
    simp [this] at ht
    omega
  have hKt : K ≤ t := by
    rw [ht] at hK
    by_contra hn
    have hl : t + 1 ≤ K := by omega
    have hh := Nat.mul_le_mul_left (alpha owner s) hl
    rw [Nat.mul_add, Nat.mul_one] at hh
    omega
  refine ⟨t, hKt, htpos, ht, ?_⟩
  simp only [coarseCounts, Equiv.symm_apply_apply, ht]
  ring



#print axioms solution
