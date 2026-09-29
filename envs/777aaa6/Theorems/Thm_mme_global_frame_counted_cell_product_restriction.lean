-- Prove2me | Theorems.Thm_mme_global_frame_counted_cell_product_restriction
-- name    : mme_global_frame_counted_cell_product_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:11:58.092317+00:00
-- url     : https://prove2.me/theorems/5a3cdeac-e3da-4aa1-8349-3498761f9f4a
-- title:
--   Global histogram frame counts determine the extracted cell tensor sizes
-- statement:
--   The product of graded cell histogram tensors, with each tensor length equal to its prescribed frame count, restricts from the actual flat profiled tensor of a global CW histogram frame. Membership of the reference address in the exact target proves every cell fiber cardinality; no partition or fiber-size assumption is required. Every cell retains the global normalization, including zero-count cells.
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

theorem mme_global_frame_counted_cell_product_restriction
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
            ∀ a, |(count (fun _ : Fin (D.m (d j).1 (d j).2) => Unit.unit)
                (label 5 ell (D.m (d j).1 (d j).2) (Equiv.refl _) x) Unit.unit a : ℝ) / D.L -
              center i (d j) a| ≤ eps)))
      (ProfiledCW.tensor K (D.window (fun i hist => ∀ c a,
        |(hist c a : ℝ) / D.L - center i c a| ≤ eps))) := by sorry
