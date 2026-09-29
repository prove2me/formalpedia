-- Prove2me | Theorems.Thm_mme_global_frame_normalized_cell_product_restriction
-- name    : mme_global_frame_normalized_cell_product_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:16:48.99518+00:00
-- url     : https://prove2.me/theorems/cff6b505-1028-40a8-98bd-ef0b069a3239
-- title:
--   Global frame extraction with normalized positive cells and exact empty-cell constraints
-- statement:
--   A global histogram frame supplies its counted graded cell product with each positive cell normalized by its own count. Centers and tolerances scale by the global length divided by the cell count. Empty cells impose exactly the absolute-center bound. Global length positivity follows from the frame itself; no positive-cell-count hypothesis is assumed.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Definitions.Def_mme_global_CW_histogram_frame
import Theorems.Thm_mme_basis_projected_family_restrict
import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit Module PiTensorProduct
open scoped Classical
set_option autoImplicit false
universe u
universe v w

theorem mme_global_frame_normalized_cell_product_restriction
    {K : Type u} [Field K] {ell M : ℕ} (D : GlobalCW.HistogramFrame ell M)
    {parts : ℕ} (d : Fin parts ≃ Cell D.degree D.R D.bounds)
    (center : Fin 3 → Cell D.degree D.R D.bounds → CompleteWord ell → ℝ)
    (eps : ℝ) :
    Restrict
      (kronFin parts (fun j =>
        (source K 5 ell (D.m (d j).1 (d j).2)).basisAllAllowedSubtensor
          (basis K 5 ell (D.m (d j).1 (d j).2)) (fun i x =>
            (∀ r, grade (label 5 ell (D.m (d j).1 (d j).2) (Equiv.refl _) x r) =
              ((d j).2.val i).val) ∧
            if D.m (d j).1 (d j).2 = 0 then ∀ a, |center i (d j) a| ≤ eps else
            ∀ a, |(count (fun _ : Fin (D.m (d j).1 (d j).2) => Unit.unit)
                (label 5 ell (D.m (d j).1 (d j).2) (Equiv.refl _) x) Unit.unit a : ℝ) / (D.m (d j).1 (d j).2 : ℝ) -
              ((D.L : ℝ) / D.m (d j).1 (d j).2) * center i (d j) a| ≤
                ((D.L : ℝ) / D.m (d j).1 (d j).2) * eps)))
      (ProfiledCW.tensor K (D.window (fun i hist => ∀ c a,
        |(hist c a : ℝ) / D.L - center i c a| ≤ eps))) := by sorry
