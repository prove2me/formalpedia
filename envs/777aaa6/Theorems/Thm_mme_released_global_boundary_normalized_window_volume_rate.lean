-- Prove2me | Theorems.Thm_mme_released_global_boundary_normalized_window_volume_rate
-- name    : mme_released_global_boundary_normalized_window_volume_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T03:00:29.704744+00:00
-- url     : https://prove2.me/theorems/9b313c74-2ed4-4f69-8596-963087f47917
-- title:
--   Released global boundary windows attain their entropy volume rate
-- statement:
--   Every positive-mass released global boundary cell has matrix extractions whose logarithmic volume eventually attains the entropy and CW-letter rate of its exact histogram, with arbitrarily small linear loss. The replication threshold and extracted boundary profile work for every nonnegative normalized-window tolerance.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_basis_projected_family_restrict
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj MME.RecursiveYZ.Boundary
open Filter
open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_boundary_normalized_window_volume_rate
    (owner : Fin 6) (c : Cell 8 1 (fun _ _ ↦ 8))
    (hmass : 0 < coarseCounts owner c.2) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 3
        (coarseCounts owner c.2),
      (∀ i w, wordCounts owner i c.2 w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ C : Boundary.Profile 3
          (k * (coarseCounts owner c.2)),
        0 < C.dim ∧ C.a z * C.b z * C.c z = C.dim ∧
        (∀ i, (c.2.val i).val = C.shape z i) ∧
        (∀ i w, k * wordCounts owner i c.2 w = C.mu z i w) ∧
        (k : ℝ) *
          (((coarseCounts owner c.2 : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((coarseCounts owner c.2 : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.a z * C.b z * C.c z : ℕ) ∧
        ∀ (eps : ℝ), 0 ≤ eps → ∀ (K : Type u) [Field K],
          let L := k * coarseCounts owner c.2
          Restrict (MMObj K (C.a z) (C.b z) (C.c z))
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
        (∀ r, CWCells.grade (label 5 3 L (Equiv.refl _) x r) = (c.2.val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i c w| ≤ eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
          ((blocks k : ℝ) / (L : ℝ)) * (profile owner).2 i c w| ≤
          ((blocks k : ℝ) / (L : ℝ)) * eps)) := by sorry
