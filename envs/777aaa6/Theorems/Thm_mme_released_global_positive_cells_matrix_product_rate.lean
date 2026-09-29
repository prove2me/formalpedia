-- Prove2me | Theorems.Thm_mme_released_global_positive_cells_matrix_product_rate
-- name    : mme_released_global_positive_cells_matrix_product_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:43:10.832473+00:00
-- url     : https://prove2.me/theorems/097345c3-f662-40d2-86d7-6ea41263a0a0
-- title:
--   Only positive-mass cell extractions are needed for the released global matrix product
-- statement:
--   At a common positive global replication and nonnegative tolerance, extraction proofs for every positive-mass normalized cell combine into a positive matrix family in the actual sixfold symmetrized global histogram tensor. The logarithmic weight bound is the sum of the positive-cell rates; all zero-mass cells are supplied automatically by scalar matrix extractions. This theorem does not establish the remaining positive-cell extractions or select common scales.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_sixSymmetrization_restrict
import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_histogram_frame
import Theorems.Thm_mme_basis_projected_family_restrict
import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_rank_bridge
open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit Module PiTensorProduct
open scoped Classical
open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_positive_cells_matrix_product_rate
    {K : Type u} [Field K] (owner : Fin 6) (k : ℕ) (hk : 0 < k)
    (reference : MME.ReleasedGlobal.Reference owner k)
    {parts : ℕ} (d : Fin parts ≃ Cell 8 1 (fun _ _ ↦ 8))
    (eps : ℝ) (heps : 0 ≤ eps) (tau : ℝ) (rate : Fin parts → ℝ) :
    let cell := fun j : Fin parts =>
        (source K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2))).basisAllAllowedSubtensor
          (basis K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2))) (fun i x =>
            (∀ r, grade (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (Equiv.refl _) x r) =
              ((d j).2.val i).val) ∧
            if (k * MME.ReleasedGlobal.coarseCounts owner (d j).2) = 0 then ∀ a, |(MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤ eps else
            ∀ a, |(count (fun _ : Fin ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) => Unit.unit)
                (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (Equiv.refl _) x) Unit.unit a : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ) -
              ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ)) * (MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤
                ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ)) * eps)
    (∀ j, 0 < MME.ReleasedGlobal.coarseCounts owner (d j).2 → ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
      Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
        (sixSymmetrization (cell j)) ∧
      Real.exp (rate j) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ) ^ tau) →
    ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
      Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
        (sixSymmetrization (ProfiledCW.tensor K
          ((MME.ReleasedGlobal.frame owner k hk reference).window
            (MME.ReleasedGlobal.windowGood owner k eps)))) ∧
      Real.exp (∑ j, if 0 < MME.ReleasedGlobal.coarseCounts owner (d j).2 then rate j else 0) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ) ^ tau := by sorry
