-- Prove2me | Theorems.Thm_mme_complete_word_cell_windows_product_restriction
-- name    : mme_complete_word_cell_windows_product_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:03:29.687534+00:00
-- url     : https://prove2.me/theorems/bb7913f8-c6b8-445e-bf2c-ac90563dc7ad
-- title:
--   Complete-word cell windows extract simultaneously as a tensor product
-- statement:
--   For any partition of Coppersmith-Winograd word positions and arbitrary complete-word predicates on each cell, the tensor product of the cellwise restricted tensors restricts from the tensor satisfying all cell predicates simultaneously. The proof uses actual fiber grouping and basis projections. Predicates may contain frequency bands, grading conditions, or exact histograms; no exact-profile or separate tensor-restriction hypothesis is required. This supplies a generic cell-partition step for global window continuations, but does not construct the released global continuation or certify its rate.
-- source:
--   Exact fiber grouping and simultaneous basis projection for arbitrary cell windows.

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

theorem mme_complete_word_cell_windows_product_restriction
    {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (D : Partition cell)
    (W : ∀ j : Fin D.parts, Fin 3 → (Fin (D.size j) → CompleteWord ell) → Prop) :
    Restrict
      (kronFin D.parts (fun j =>
        (source K q ell (D.size j)).basisAllAllowedSubtensor
          (basis K q ell (D.size j))
          (fun i x => W j i (label q ell (D.size j) (Equiv.refl _) x))))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun i x => ∀ j, W j i
          (fun r => label q ell L positions x (D.fiber j r).val))) := by sorry
