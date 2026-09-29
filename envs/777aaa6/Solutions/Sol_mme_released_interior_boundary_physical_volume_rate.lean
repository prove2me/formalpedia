-- Prove2me | solution 1 for mme_released_interior_boundary_physical_volume_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:55:30.19505+00:00
-- url     : https://prove2.me/submissions/05b2766a-51ba-4d35-970c-bb70c9553e3d

import Theorems.Thm_mme_released_interior_physical_boundary_matrix_extraction
import Theorems.Thm_mme_boundary_scaled_volume_rate
import Mathlib.Tactic.FinCases

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary MME.ReleasedInterior Filter
universe u

private theorem boundary_count_from_mu {ell L M : ℕ}
    (B : Boundary.Profile ell L) (C : Boundary.Profile ell M)
    (z : Fin 3) (k : ℕ) (h : ∀ i w, C.mu z i w = B.mu z i w * k) :
    ∀ w, C.count w = B.count w * k := by
  intro w
  fin_cases z
  · simpa [Boundary.Profile.mu] using h 1 w
  · simpa [Boundary.Profile.mu] using h 2 w
  · simpa [Boundary.Profile.mu] using h 0 w

/-- Each released boundary cell has physical matrix extractions attaining the
entropy and CW-letter rate of its exact integer histogram. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (c : Cell 4 6 (parent s)) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (hmass : 0 < splitCount owner s c.1 c.2 +
      splitCount owner s c.1 (complement (parent_total s c.1) c.2))
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
  have hbase := mme_released_interior_physical_boundary_matrix_extraction.{u} owner s hi 1 c z hz
  rw [Nat.one_mul] at hbase
  simp only [Nat.one_mul] at hbase
  obtain ⟨B, _, _, _, hBmu, _⟩ := hbase
  refine ⟨B, hBmu, ?_⟩
  have hrate := mme_boundary_scaled_volume_rate B hmass
    delta hdelta
  have hrate' : ∀ᶠ k : ℕ in atTop,
      ∀ C : Boundary.Profile 2 (k * (splitCount owner s c.1 c.2 +
          splitCount owner s c.1 (complement (parent_total s c.1) c.2))),
        (∀ w, C.count w = B.count w * k) →
        (k : ℝ) *
          (((splitCount owner s c.1 c.2 +
              splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((splitCount owner s c.1 c.2 +
                  splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.dim : ℝ) := by
    filter_upwards [hrate] with k hk
    rw [Nat.mul_comm (splitCount owner s c.1 c.2 +
      splitCount owner s c.1 (complement (parent_total s c.1) c.2)) k] at hk
    exact hk
  filter_upwards [hrate'] with k hk
  obtain ⟨C, hpos, hvol, hshape, hmu, hextract⟩ :=
    mme_released_interior_physical_boundary_matrix_extraction owner s hi k c z hz
  have hcount := boundary_count_from_mu B C z k (by
    intro i w
    rw [← hmu i w, ← hBmu i w, Nat.mul_comm])
  refine ⟨C, hpos, hvol, hshape, hmu, ?_, hextract⟩
  rw [hvol]
  exact hk C hcount


#print axioms solution
