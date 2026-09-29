-- Prove2me | Theorems.Thm_mme_released_global_boundary_normalized_window_matrix_extraction
-- name    : mme_released_global_boundary_normalized_window_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:58:20.38176+00:00
-- url     : https://prove2.me/theorems/dce0ead9-d411-4054-8031-fbcc053fda23
-- title:
--   Positive released global boundary windows admit matrix extraction
-- statement:
--   Every positive-length released coarse cell with a zero coordinate admits a positive-dimensional matrix extraction from its actual normalized histogram window, across all six owners and at every nonnegative tolerance.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_basis_projected_family_restrict
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj MME.RecursiveYZ.Boundary
open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_boundary_normalized_window_matrix_extraction
    (owner : Fin 6) (k : ℕ) (c : Cell 8 1 (fun _ _ ↦ 8))
    (hL : 0 < k * coarseCounts owner c.2) (z : Fin 3)
    (hz : (c.2.val z).val = 0) (eps : ℝ) (heps : 0 ≤ eps) :
    ∃ B : Boundary.Profile 3 (k * coarseCounts owner c.2),
      0 < B.dim ∧ B.a z * B.b z * B.c z = B.dim ∧
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i w, k * wordCounts owner i c.2 w = B.mu z i w) ∧
      ∀ (K : Type u) [Field K],
      let L := k * coarseCounts owner c.2
      Restrict (MMObj K (B.a z) (B.b z) (B.c z))
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
        (∀ r, CWCells.grade (label 5 3 L (Equiv.refl _) x r) = (c.2.val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i c w| ≤ eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
          ((blocks k : ℝ) / (L : ℝ)) * (profile owner).2 i c w| ≤
          ((blocks k : ℝ) / (L : ℝ)) * eps)) := by sorry
