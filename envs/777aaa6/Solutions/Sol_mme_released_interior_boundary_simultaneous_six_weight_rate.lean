-- Prove2me | solution 1 for mme_released_interior_boundary_simultaneous_six_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:16:43.291464+00:00
-- url     : https://prove2.me/submissions/255540cd-f639-48dc-ad1c-725f89d82c53

import Theorems.Thm_mme_released_interior_boundary_all_mass_six_weight_rate

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary MME.ReleasedInterior Filter
universe u

/-- One even replication scale supports the full weight bound for every
boundary child, including empty cells, uniformly over fields and nonnegative tau. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (owner : Fin 6) (s : Fin 45)
      (c : Cell 4 6 (parent s)) (z : Fin 3),
      (seed owner s).boundary = [] → (c.2.val z).val = 0 →
    ∃ B : Boundary.Profile 2
        (splitCount owner s c.1 c.2 + splitCount owner s c.1 (complement (parent_total s c.1) c.2)),
      (∀ i w, integerProfile owner s i c w = B.mu z i w) ∧
      ∃ M : ℕ, 0 < M ∧
        (∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K M M M)
            (sixSymmetrization (CWCells.unbroken K 5 2
              ((2 * k) * (splitCount owner s c.1 c.2 +
                splitCount owner s c.1 (complement (parent_total s c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => (2 * k) * integerProfile owner s i c w)))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (6 * tau * (((2 * k : ℕ) : ℝ) *
            (((splitCount owner s c.1 c.2 +
                splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ (B.count w : ℝ) /
                  ((splitCount owner s c.1 c.2 +
                    splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ)) +
              ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by
  apply eventually_all.mpr
  intro owner
  apply eventually_all.mpr
  intro s
  apply eventually_all.mpr
  intro c
  apply eventually_all.mpr
  intro z
  by_cases hi : (seed owner s).boundary = []
  · by_cases hz : (c.2.val z).val = 0
    · obtain ⟨B, hmu, hrate⟩ :=
        mme_released_interior_boundary_all_mass_six_weight_rate.{u}
          owner s hi c z hz delta hdelta
      have hscale : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
        tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k (by decide)) tendsto_id
      exact (hscale.eventually hrate).mono fun k hk _ _ => ⟨B, hmu, hk⟩
    · exact Eventually.of_forall fun _ _ h => (hz h).elim
  · exact Eventually.of_forall fun _ h _ => (hi h).elim


#print axioms solution
