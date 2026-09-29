-- Prove2me | solution 1 for mme_released_interior_boundary_all_mass_volume_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:01:52.987984+00:00
-- url     : https://prove2.me/submissions/24f8113c-9b6e-4214-a2f8-c1a0a6edd7ac

import Theorems.Thm_mme_released_interior_boundary_physical_volume_rate

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary MME.ReleasedInterior Filter
universe u

/-- Empty boundary cells also satisfy the physical volume rate, so no
positive-mass hypothesis is needed when assembling all children. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (c : Cell 4 6 (parent s)) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 2
        (splitCount owner s c.1 c.2 + splitCount owner s c.1 (complement (parent_total s c.1) c.2)),
      (∀ i w, integerProfile owner s i c w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ C : Boundary.Profile 2
          (k * (splitCount owner s c.1 c.2 +
            splitCount owner s c.1 (complement (parent_total s c.1) c.2))),
        0 < C.dim ∧ C.a z * C.b z * C.c z = C.dim ∧
        (∀ i, (c.2.val i).val = C.shape z i) ∧
        (∀ i w, k * integerProfile owner s i c w = C.mu z i w) ∧
        (k : ℝ) *
          (((splitCount owner s c.1 c.2 +
              splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((splitCount owner s c.1 c.2 +
                  splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.a z * C.b z * C.c z : ℕ) ∧
        ∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K (C.a z) (C.b z) (C.c z))
            (CWCells.unbroken K 5 2
              (k * (splitCount owner s c.1 c.2 +
                splitCount owner s c.1 (complement (parent_total s c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => k * integerProfile owner s i c w)) := by
  classical
  by_cases hmass : 0 < splitCount owner s c.1 c.2 +
      splitCount owner s c.1 (complement (parent_total s c.1) c.2)
  · exact mme_released_interior_boundary_physical_volume_rate
      owner s hi c z hz hmass delta hdelta
  have hzero := Nat.eq_zero_of_not_pos hmass
  have hbase := mme_released_interior_physical_boundary_matrix_extraction.{u} owner s hi 1 c z hz
  rw [Nat.one_mul] at hbase
  simp only [Nat.one_mul] at hbase
  obtain ⟨B, _, _, _, hBmu, _⟩ := hbase
  have hcount : ∀ w, B.count w = 0 := by
    have htotal : ∑ w, B.count w = 0 := B.total.trans hzero
    exact fun w => (Finset.sum_eq_zero_iff.mp htotal) w (Finset.mem_univ w)
  refine ⟨B, hBmu, Eventually.of_forall fun k => ?_⟩
  obtain ⟨C, hpos, hvol, hshape, hmu, hextract⟩ :=
    mme_released_interior_physical_boundary_matrix_extraction.{u} owner s hi k c z hz
  refine ⟨C, hpos, hvol, hshape, hmu, ?_, hextract⟩
  rw [hvol]
  have hlog : 0 ≤ Real.log (C.dim : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpos)
  simp only [hzero, hcount, Nat.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
  exact le_trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k)
    (by linarith)) hlog


#print axioms solution
