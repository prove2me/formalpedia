-- Prove2me | Theorems.Thm_mme_graded_histogram_cell_windows_product_restriction
-- name    : mme_graded_histogram_cell_windows_product_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:05:58.972902+00:00
-- url     : https://prove2.me/theorems/1e82bc4e-cd26-4e50-b474-361a851d193a
-- title:
--   Graded histogram cell windows extract with the global normalization
-- statement:
--   The product of graded cell tensors with histogram bands restricts from the graded global histogram window. Exact fiber counting preserves the global denominator, centers and tolerance. Empty cells, zero tolerance and arbitrary real denominator are included using Lean division conventions; no division by cell size is required.
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

theorem mme_graded_histogram_cell_windows_product_restriction
    {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (D : Partition cell) (shape : C → Fin 3 → ℕ)
    (center : Fin 3 → C → CompleteWord ell → ℝ) (total eps : ℝ) :
    Restrict
      (kronFin D.parts (fun j =>
        (source K q ell (D.size j)).basisAllAllowedSubtensor
          (basis K q ell (D.size j)) (fun i x =>
            (∀ r, grade (label q ell (D.size j) (Equiv.refl _) x r) = shape (D.cells j) i) ∧
            ∀ a, |(count (fun _ : Fin (D.size j) => Unit.unit)
                (label q ell (D.size j) (Equiv.refl _) x) Unit.unit a : ℝ) / total -
              center i (D.cells j) a| ≤ eps)))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun i x => (∀ p, grade (label q ell L positions x p) = shape (cell p) i) ∧
          ∀ c a, |(count cell (label q ell L positions x) c a : ℝ) / total -
            center i c a| ≤ eps)) := by sorry
