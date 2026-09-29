-- Prove2me | solution 1 for mme_released_global_boundary_permuted_six_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:03:09.91306+00:00
-- url     : https://prove2.me/submissions/2f18b8de-548c-44bf-965a-25cf97b66fc5

import Theorems.Thm_mme_released_global_boundary_normalized_six_weight_rate
import Theorems.Thm_mme_sixSymmetrization_mode_permutation_iso

open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.CompleteSplit MME.TensorObj MME.RecursiveYZ.Boundary MME.RecursiveYZ.CWCells Filter
universe u
set_option autoImplicit false

/-- A whole-cell mode permutation preserves the complete boundary matrix rate,
including its histogram certificate and replication-scaled loss. -/
theorem solution
    (sigma : Equiv.Perm (Fin 3)) (owner : Fin 6) (c : Cell 8 1 (fun _ _ ↦ 8))
    (hmass : 0 < coarseCounts owner c.2) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 3
        (coarseCounts owner c.2),
      (∀ i w, wordCounts owner i c.2 w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (eps : ℝ), 0 ≤ eps → ∀ (K : Type u) [Field K],
          let L := k * coarseCounts owner c.2
          Restrict (MMObj K M M M) (sixSymmetrization (permObj sigma
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
        (∀ r, CWCells.grade (label 5 3 L (Equiv.refl _) x r) = (c.2.val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i c w| ≤ eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
          ((blocks k : ℝ) / (L : ℝ)) * (profile owner).2 i c w| ≤
          ((blocks k : ℝ) / (L : ℝ)) * eps))))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (6 * tau * ((k : ℝ) *
            (((coarseCounts owner c.2 : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ (B.count w : ℝ) /
                  ((coarseCounts owner c.2 : ℕ) : ℝ)) +
              ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by
  obtain ⟨B, hmu, hrate⟩ :=
    mme_released_global_boundary_normalized_six_weight_rate.{u}
      owner c hmass z hz delta hdelta
  refine ⟨B, hmu, ?_⟩
  filter_upwards [hrate] with k hk
  obtain ⟨M, hM, hrestrict, hweight⟩ := hk
  refine ⟨M, hM, ?_, hweight⟩
  intro eps heps K _
  exact (hrestrict eps heps K).trans
    (mme_sixSymmetrization_mode_permutation_iso _ sigma).2


#print axioms solution
