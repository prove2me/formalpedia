-- Prove2me | Theorems.Thm_mme_released_global_boundary_permuted_six_weight_rate
-- name    : mme_released_global_boundary_permuted_six_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:57:05.23858+00:00
-- url     : https://prove2.me/theorems/7de8c1e5-add6-4534-98d6-ba40654e8159
-- title:
--   Whole-cell permutations retain complete boundary rates
-- statement:
--   Every mode permutation of a normalized boundary cell preserves its sixfold matrix extraction, exact marginal certificate, and complete replication-scaled entropy and dimension rate with explicit loss. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_boundary_normalized_six_weight_rate
import Theorems.Thm_mme_sixSymmetrization_mode_permutation_iso
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.CompleteSplit MME.TensorObj MME.RecursiveYZ.Boundary MME.RecursiveYZ.CWCells Filter
universe u

theorem mme_released_global_boundary_permuted_six_weight_rate
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
            ((M * M * M : ℕ) : ℝ) ^ tau := by sorry
