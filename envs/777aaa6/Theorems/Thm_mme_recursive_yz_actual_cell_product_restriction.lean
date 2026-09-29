-- Prove2me | Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction
-- name    : mme_recursive_yz_actual_cell_product_restriction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T12:07:59.989061+00:00
-- url     : https://prove2.me/theorems/b99dbc2e-63f7-4284-bc7b-99e47c2d107c
-- title:
--   Literal intact CW templates extract their exact product of cell-profile tensors
-- statement:
--   Let U be a literal CW power restricted to the prescribed grade and exact full fine-word histogram in every physical cell, in all three modes. For any enumeration of all cells and their position fibers, the tensor product of the literal cell tensors restricts to U. Every child position is retained, and each cell tensor has its exact fiber multiplicity and the same complete-word histogram. This conversion incurs no additional copy-count loss and includes empty cells.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6.SS5, Section 6.5 displayed intact tensor; the restriction direction required by recursive assembly.

import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_CW_2376_address_block
open MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u v w

theorem mme_recursive_yz_actual_cell_product_restriction {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (D : Partition cell) :
    Restrict (kronFin D.parts (D.piece K q ell shape mu))
      (unbroken K q ell L positions cell shape mu)  := by sorry
