-- Prove2me | Theorems.Thm_mme_normalized_histogram_cell_windows_product_restriction
-- name    : mme_normalized_histogram_cell_windows_product_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:06:03.447175+00:00
-- url     : https://prove2.me/theorems/168a1f66-e6cd-465b-9e7c-6f2db25512ed
-- title:
--   Cell-normalized histogram bands extract after exact tolerance rescaling
-- statement:
--   For a positive global normalization and positive cell sizes, the product of graded cell tensors normalized by their own cell sizes restricts from the graded global histogram window. Each cell center and tolerance is multiplied by global total divided by that cell size. Actual tensor maps are constructed by exact fiber grouping and basis projection; no exact-histogram or restriction hypotheses are assumed.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

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

theorem mme_normalized_histogram_cell_windows_product_restriction
    {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (D : Partition cell) (shape : C → Fin 3 → ℕ)
    (center : Fin 3 → C → CompleteWord ell → ℝ) (total eps : ℝ)
    (htotal : 0 < total) (hsizes : ∀ j, 0 < D.size j) :
    Restrict
      (kronFin D.parts (fun j =>
        (source K q ell (D.size j)).basisAllAllowedSubtensor
          (basis K q ell (D.size j)) (fun i x =>
            (∀ r, grade (label q ell (D.size j) (Equiv.refl _) x r) = shape (D.cells j) i) ∧
            ∀ a, |(count (fun _ : Fin (D.size j) => Unit.unit)
                (label q ell (D.size j) (Equiv.refl _) x) Unit.unit a : ℝ) / (D.size j : ℝ) -
              (total / (D.size j : ℝ)) * center i (D.cells j) a| ≤
                (total / (D.size j : ℝ)) * eps)))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun i x => (∀ p, grade (label q ell L positions x p) = shape (cell p) i) ∧
          ∀ c a, |(count cell (label q ell L positions x) c a : ℝ) / total -
            center i c a| ≤ eps)) := by sorry
