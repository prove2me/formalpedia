-- Prove2me | Definitions.Def_mme_recursive_yz_cell_partition
-- name    : mme_recursive_yz_cell_partition
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T12:01:24.605528+00:00
-- url     : https://prove2.me/theorems/24b27f9f-ce83-49bf-8805-86000bd30efe
-- title:
--   Exact physical cell partitions and literal child-profile CW tensors
-- statement:
--   A physical cell partition enumerates every cell and gives a bijection between each cell’s child positions and a finite interval of its exact size. The canonical partition uses the actual fibers of the cell map, including empty fibers. It induces a bijection of all elementary CW positions by preserving the fine position within each child. Each cell piece is the literal CW power projected onto its prescribed grade and exact complete-word histogram in all three modes.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6.SS5, Section 6.5 displayed intact tensor and its physical cell multiplicities.

import Definitions.Def_mme_recursive_yz_CW_cells
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum

open MME MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u v w
namespace MME.RecursiveYZ.CWCells

/-- An enumeration of every physical cell and all of its child positions. -/
structure Partition {P : Type v} {C : Type w} (cell : P → C) where
  parts : ℕ
  cells : Fin parts ≃ C
  size : Fin parts → ℕ
  fiber : ∀ j, Fin (size j) ≃ {p : P // cell p = cells j}

noncomputable def Partition.canonical {P : Type v} {C : Type w}
    [Fintype P] [Fintype C] (cell : P → C) : Partition cell := by
  classical
  exact {
    parts := Fintype.card C
    cells := (Fintype.equivFin C).symm
    size := fun j ↦ Fintype.card {p : P // cell p = (Fintype.equivFin C).symm j}
    fiber := fun j ↦ (Fintype.equivFin _).symm }

noncomputable def Partition.positions {P : Type v} {C : Type w}
    {cell : P → C} (D : Partition cell) : (Σ j, Fin (D.size j)) ≃ P :=
  (Equiv.sigmaCongr D.cells D.fiber).trans (Equiv.sigmaFiberEquiv cell)

@[simp] theorem Partition.positions_apply {P : Type v} {C : Type w}
    {cell : P → C} (D : Partition cell) (j : Fin D.parts) (r : Fin (D.size j)) :
    D.positions ⟨j,r⟩ = (D.fiber j r).val := rfl

/-- The grouped elementary factors, retaining their order inside each child. -/
noncomputable def Partition.leaves {P : Type v} {C : Type w}
    {cell : P → C} (D : Partition cell) (ell L : ℕ) (e : Fin L ≃ P) :
    (Σ j, Fin (D.size j * 2 ^ (ell - 1))) ≃ Fin (L * 2 ^ (ell - 1)) :=
  (Equiv.sigmaCongrRight (fun _ ↦ finProdFinEquiv.symm)).trans
    ((Equiv.sigmaProdDistrib (fun j ↦ Fin (D.size j)) (Fin (2 ^ (ell - 1)))).symm.trans
      ((Equiv.prodCongr (D.positions.trans e.symm) (Equiv.refl _)).trans finProdFinEquiv))

/-- One literal CW cell power with its exact fine-word profiles in all modes. -/
noncomputable def Partition.piece {P : Type v} {C : Type w}
    {cell : P → C} (D : Partition cell) (K : Type u) [Field K] (q ell : ℕ)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (j : Fin D.parts) : TensorObj K 3 :=
  unbroken K q ell (D.size j) (Equiv.refl _) (fun _ ↦ Unit.unit)
    (fun _ ↦ shape (D.cells j)) (fun i _ ↦ mu i (D.cells j))

end MME.RecursiveYZ.CWCells


