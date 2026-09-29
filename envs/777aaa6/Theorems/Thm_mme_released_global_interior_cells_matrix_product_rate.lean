-- Prove2me | Theorems.Thm_mme_released_global_interior_cells_matrix_product_rate
-- name    : mme_released_global_interior_cells_matrix_product_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T03:10:03.350428+00:00
-- url     : https://prove2.me/theorems/32c6831f-c2bc-4bee-b039-b24000067ef1
-- title:
--   Global released matrix product requires only positive interior-cell extractions
-- statement:
--   After a common replication threshold, the released global histogram tensor admits a positive matrix family with the summed rates whenever its positive interior cells admit their prescribed matrix families. Positive boundary cells are supplied by their exact histogram entropy and CW-letter rates, and empty cells contribute zero. The boundary threshold works for every nonnegative tolerance and tau.
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
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Definitions.Def_mme_recursive_yz_owned_filters
open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit Module PiTensorProduct
open scoped Classical
open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj MME.RecursiveYZ.Boundary
open Filter
open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_interior_cells_matrix_product_rate
    {K : Type u} [Field K] (owner : Fin 6)
    {parts : ℕ} (d : Fin parts ≃ Cell 8 1 (fun _ _ ↦ 8))
    (boundary : Fin parts → Bool)
    (hboundary : ∀ j, boundary j = true ↔
      0 < coarseCounts owner (d j).2 ∧ ∃ z : Fin 3, ((d j).2.val z).val = 0)
    (z : {j : Fin parts // boundary j = true} → Fin 3)
    (hz : ∀ j, ((d j.val).2.val (z j)).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : ∀ j : {j : Fin parts // boundary j = true},
        Boundary.Profile 3 (coarseCounts owner (d j.val).2),
      (∀ j i w, wordCounts owner i (d j.val).2 w = (B j).mu (z j) i w) ∧
      ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
        (reference : MME.ReleasedGlobal.Reference owner k)
        (eps : ℝ) (heps : 0 ≤ eps) (tau : ℝ) (htau : 0 ≤ tau)
        (rate : Fin parts → ℝ),
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
    let combined := fun j : Fin parts => if hj : boundary j = true then
      6 * tau * ((k : ℝ) *
          ((coarseCounts owner (d j).2 : ℝ) * Real.log 2 *
            mme_modern_entropyBits (fun w => ((B ⟨j, hj⟩).count w : ℝ) /
              (coarseCounts owner (d j).2 : ℝ)) +
            ((∑ w, (B ⟨j, hj⟩).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta)) else rate j
    (∀ j, 0 < coarseCounts owner (d j).2 →
      (∀ i : Fin 3, 0 < ((d j).2.val i).val) →
      ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
        Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
          (sixSymmetrization (cell j)) ∧
        Real.exp (rate j) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ) ^ tau) →
    ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
      Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
        (sixSymmetrization (ProfiledCW.tensor K
          ((MME.ReleasedGlobal.frame owner k hk reference).window
            (MME.ReleasedGlobal.windowGood owner k eps)))) ∧
      Real.exp (∑ j, if 0 < coarseCounts owner (d j).2 then combined j else 0) ≤
        ∑ v, ((a v * b v * c v : ℕ) : ℝ) ^ tau := by sorry
