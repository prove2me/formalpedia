-- Prove2me | solution 1 for mme_released_interior_boundary_six_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:01:52.431397+00:00
-- url     : https://prove2.me/submissions/b19aaa48-d9af-46d0-a98a-f470bf3fe13c

import Theorems.Thm_mme_released_interior_boundary_physical_volume_rate
import Theorems.Thm_mme_matrix_extraction_six_volume_weight

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary MME.ReleasedInterior Filter
universe u

/-- The released boundary cells supply square matrices in the full
six-symmetric physical tensor, with their entropy and letter weight. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (c : Cell 4 6 (parent s)) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (hmass : 0 < splitCount owner s c.1 c.2 +
      splitCount owner s c.1 (complement (parent_total s c.1) c.2))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 2
        (splitCount owner s c.1 c.2 + splitCount owner s c.1 (complement (parent_total s c.1) c.2)),
      (∀ i w, integerProfile owner s i c w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K M M M)
            (sixSymmetrization (CWCells.unbroken K 5 2
              (k * (splitCount owner s c.1 c.2 +
                splitCount owner s c.1 (complement (parent_total s c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => k * integerProfile owner s i c w)))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (6 * tau * ((k : ℝ) *
            (((splitCount owner s c.1 c.2 +
                splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ (B.count w : ℝ) /
                  ((splitCount owner s c.1 c.2 +
                    splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ)) +
              ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by
  obtain ⟨B, hmu, hrate⟩ :=
    mme_released_interior_boundary_physical_volume_rate.{u} owner s hi c z hz hmass delta hdelta
  refine ⟨B, hmu, ?_⟩
  filter_upwards [hrate] with k hk
  obtain ⟨C, hpos, hvol, _, _, hlog, hextract⟩ := hk
  have hv : 0 < C.a z * C.b z * C.c z := by rw [hvol]; exact hpos
  refine ⟨(C.a z * C.b z * C.c z) ^ 2, pow_pos hv _, ?_, ?_⟩
  · intro K _
    exact (mme_matrix_extraction_six_volume_weight (K := K)
      (C.a z) (C.b z) (C.c z) (hextract K) hv _ 0 le_rfl hlog).1
  · intro tau htau
    exact (mme_matrix_extraction_six_volume_weight (K := ULift.{u} ℚ)
      (C.a z) (C.b z) (C.c z) (hextract (ULift.{u} ℚ)) hv _ tau htau hlog).2


#print axioms solution
