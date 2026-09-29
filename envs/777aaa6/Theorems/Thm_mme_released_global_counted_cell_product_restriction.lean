-- Prove2me | Theorems.Thm_mme_released_global_counted_cell_product_restriction
-- name    : mme_released_global_counted_cell_product_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:14:23.720454+00:00
-- url     : https://prove2.me/theorems/c3f78af0-3257-4896-913d-2105d0902b65
-- title:
--   Released global profile windows supply the full counted coarse-cell product
-- statement:
--   For every owner, positive scale and reference address of the released global construction, the actual global profile window supplies the product of all coarse-cell graded histogram tensors. Each cell has length k times its released coarse count. Centers are the released profile and counts retain the global block denominator. Zero-count cells are retained; no tensor restriction or partition hypothesis is assumed.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Definitions.Def_mme_released_global_frame_data
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

theorem mme_released_global_counted_cell_product_restriction
    {K : Type u} [Field K] (owner : Fin 6) (k : ℕ) (hk : 0 < k)
    (a : MME.ReleasedGlobal.Reference owner k)
    {parts : ℕ} (d : Fin parts ≃ Cell 8 1 (fun _ _ ↦ 8))
    (eps : ℝ) :
    Restrict
      (kronFin parts (fun j =>
        (source K 5 3 (k * MME.ReleasedGlobal.coarseCounts owner (d j).2)).basisAllAllowedSubtensor
          (basis K 5 3 (k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (fun i x =>
            (∀ r, grade (label 5 3 (k * MME.ReleasedGlobal.coarseCounts owner (d j).2) (Equiv.refl _) x r) =
              ((d j).2.val i).val) ∧
            ∀ a, |(count (fun _ : Fin (k * MME.ReleasedGlobal.coarseCounts owner (d j).2) => Unit.unit)
                (label 5 3 (k * MME.ReleasedGlobal.coarseCounts owner (d j).2) (Equiv.refl _) x) Unit.unit a : ℝ) / MME.ReleasedGlobal.blocks k -
              (MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤ eps)))
      (ProfiledCW.tensor K ((MME.ReleasedGlobal.frame owner k hk a).window
        (MME.ReleasedGlobal.windowGood owner k eps))) := by sorry
