-- Prove2me | solution 1 for mme_released_recursive_positive_child_reindex
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T04:23:09.556292+00:00
-- url     : https://prove2.me/submissions/6faa92c2-75fa-48ad-8f63-3e44f795cf8e

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_joint_interior_profiles
import Theorems.Thm_mme_released_recursive_level2_marginals

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators
open MME MME.RecursiveYZ MME.CompleteSplit

/- The released recursive tables are due to marwahaha. This proof supplies the
   finite reindexing between their regional and pooled presentations. The closed
   level-two marginal formula is used through its canonical public theorem. -/
namespace RecursiveContinuationReindex

abbrev ChildCell := (region : Fin 6) × Cell 4 88 (RecStage.parent3 region)
abbrev Code := Fin 6 × Fin 88 × Fin 3

def childMass (cell : ChildCell) : ℕ :=
  RecStage.m3 cell.1 cell.2.1 cell.2.2 +
    RecStage.m3 cell.1 cell.2.1
      (complement (RecStage.htotal3 cell.1 cell.2.1) cell.2.2)

abbrev PositiveChild := {cell : ChildCell //
  (∀ i : Fin 3, 0 < (cell.2.2.val i).val) ∧ 0 < childMass cell}

private def shape (double : Fin 3) (i : Fin 3) : Fin 5 :=
  if i = double then 2 else 1

private theorem shape_sum : ∀ double : Fin 3,
    (shape double 0).val + (shape double 1).val + (shape double 2).val = 4 := by
  decide +kernel

private theorem shape_positive : ∀ double i : Fin 3, 0 < (shape double i).val := by
  decide +kernel

private def doubleIndex (f : Fin 3 → Fin 5) : Fin 3 :=
  if (f 0).val = 2 then 0 else if (f 1).val = 2 then 1 else 2

private theorem doubleIndex_shape : ∀ double : Fin 3,
    doubleIndex (shape double) = double := by
  decide +kernel

private theorem shape_of_positive (f : Fin 3 → Fin 5)
    (hsum : (f 0).val + (f 1).val + (f 2).val = 4)
    (hpositive : ∀ i, 0 < (f i).val) : shape (doubleIndex f) = f := by
  have h0 := hpositive 0
  have h1 := hpositive 1
  have h2 := hpositive 2
  funext i
  apply Fin.ext
  by_cases hfirst : (f 0).val = 2
  · fin_cases i <;> simp [shape, doubleIndex, hfirst] <;> omega
  · by_cases hsecond : (f 1).val = 2
    · fin_cases i <;> simp [shape, doubleIndex, hfirst, hsecond] <;> omega
    · fin_cases i <;> simp [shape, doubleIndex, hfirst, hsecond] <;> omega

private def Admissible (code : Code) : Prop :=
  ∀ i : Fin 3, (shape code.2.2 i).val ≤ RecStage.parent3 code.1 code.2.1 i

private instance (code : Code) : Decidable (Admissible code) :=
  inferInstanceAs (Decidable (∀ i : Fin 3,
    (shape code.2.2 i).val ≤ RecStage.parent3 code.1 code.2.1 i))

private def cellOfCode (code : Code) (h : Admissible code) : ChildCell :=
  ⟨code.1, code.2.1, ⟨shape code.2.2, shape_sum code.2.2, h⟩⟩

private def codeOfCell (cell : ChildCell) : Code :=
  (cell.1, cell.2.1, doubleIndex cell.2.2.val)

private theorem codeOf_cellOf (code : Code) (h : Admissible code) :
    codeOfCell (cellOfCode code h) = code := by
  rcases code with ⟨region, row, double⟩
  simp only [codeOfCell, cellOfCode, doubleIndex_shape]

private theorem codeOf_admissible (cell : ChildCell)
    (hpositive : ∀ i, 0 < (cell.2.2.val i).val) : Admissible (codeOfCell cell) := by
  intro i
  change (shape (doubleIndex cell.2.2.val) i).val ≤ _
  rw [shape_of_positive cell.2.2.val cell.2.2.property.1 hpositive]
  exact cell.2.2.property.2 i

private theorem cellOf_codeOf (cell : ChildCell)
    (hpositive : ∀ i, 0 < (cell.2.2.val i).val) :
    cellOfCode (codeOfCell cell) (codeOf_admissible cell hpositive) = cell := by
  rcases cell with ⟨region, row, split⟩
  exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq
    (Subtype.ext (shape_of_positive split.val split.property.1 hpositive)))))

private theorem cellOf_congr {code other : Code} (heq : code = other)
    (hcode : Admissible code) (hother : Admissible other) :
    cellOfCode code hcode = cellOfCode other hother := by
  cases heq
  rfl

private def joinRow (block : Fin 69) (offset : Fin 16) : Fin 1104 :=
  ⟨16 * block.val + offset.val, by omega⟩

private def rowBlock (row : Fin 1104) : Fin 69 := ⟨row.val / 16, by omega⟩
private def rowOffset (row : Fin 1104) : Fin 16 :=
  ⟨row.val % 16, Nat.mod_lt _ (by decide)⟩

private theorem join_split (row : Fin 1104) :
    joinRow (rowBlock row) (rowOffset row) = row := by
  apply Fin.ext
  dsimp [joinRow, rowBlock, rowOffset]
  omega

private def codeBlock0 : Fin 16 → Code :=
  ![(0, 0, 2), (1, 0, 1), (2, 0, 2), (3, 0, 1), (4, 0, 0), (5, 0, 0), (0, 1, 2), (0, 1, 1), (2, 1, 2), (2, 1, 0), (3, 1, 1), (3, 1, 0), (0, 2, 2), (0, 2, 1), (2, 2, 2), (2, 2, 0)]

private def codeBlock1 : Fin 16 → Code :=
  ![(3, 2, 1), (3, 2, 0), (1, 1, 1), (1, 1, 2), (4, 1, 0), (4, 1, 2), (5, 1, 0), (5, 1, 1), (0, 3, 2), (0, 3, 1), (1, 2, 1), (1, 2, 2), (2, 3, 2), (2, 3, 0), (4, 2, 0), (4, 2, 2)]

private def codeBlock2 : Fin 16 → Code :=
  ![(5, 2, 0), (5, 2, 1), (0, 4, 1), (1, 3, 2), (2, 4, 0), (3, 3, 0), (4, 3, 2), (5, 3, 1), (0, 5, 2), (0, 5, 0), (1, 4, 1), (1, 4, 0), (2, 5, 2), (2, 5, 1), (0, 6, 2), (0, 6, 1)]

private def codeBlock3 : Fin 16 → Code :=
  ![(0, 6, 0), (1, 5, 1), (1, 5, 2), (1, 5, 0), (2, 6, 2), (2, 6, 0), (2, 6, 1), (3, 4, 1), (3, 4, 0), (3, 4, 2), (2, 7, 2), (2, 7, 0), (2, 7, 1), (3, 5, 1), (3, 5, 0), (3, 5, 2)]

private def codeBlock4 : Fin 16 → Code :=
  ![(4, 4, 0), (4, 4, 2), (4, 4, 1), (5, 4, 0), (5, 4, 1), (5, 4, 2), (0, 7, 2), (0, 7, 1), (0, 7, 0), (1, 6, 1), (1, 6, 2), (1, 6, 0), (2, 8, 2), (2, 8, 0), (2, 8, 1), (3, 6, 1)]

private def codeBlock5 : Fin 16 → Code :=
  ![(3, 6, 0), (3, 6, 2), (4, 5, 0), (4, 5, 2), (4, 5, 1), (5, 5, 0), (5, 5, 1), (5, 5, 2), (0, 8, 1), (0, 8, 0), (1, 7, 2), (1, 7, 0), (3, 7, 0), (3, 7, 2), (4, 6, 2), (4, 6, 1)]

private def codeBlock6 : Fin 16 → Code :=
  ![(5, 6, 1), (5, 6, 2), (0, 9, 2), (0, 9, 0), (1, 8, 1), (1, 8, 0), (2, 9, 2), (2, 9, 1), (0, 10, 2), (0, 10, 1), (0, 10, 0), (1, 9, 1), (1, 9, 2), (1, 9, 0), (4, 7, 0), (4, 7, 2)]

private def codeBlock7 : Fin 16 → Code :=
  ![(4, 7, 1), (5, 7, 0), (5, 7, 1), (5, 7, 2), (0, 11, 2), (0, 11, 1), (0, 11, 0), (1, 10, 1), (1, 10, 2), (1, 10, 0), (2, 10, 2), (2, 10, 0), (2, 10, 1), (3, 8, 1), (3, 8, 0), (3, 8, 2)]

private def codeBlock8 : Fin 16 → Code :=
  ![(0, 12, 1), (0, 12, 0), (1, 11, 2), (1, 11, 0), (4, 8, 2), (4, 8, 1), (3, 9, 1), (3, 9, 2), (4, 9, 0), (4, 9, 1), (5, 8, 0), (5, 8, 2), (0, 13, 2), (0, 13, 1), (0, 13, 0), (1, 12, 1)]

private def codeBlock9 : Fin 16 → Code :=
  ![(1, 12, 2), (1, 12, 0), (2, 11, 2), (2, 11, 0), (2, 11, 1), (4, 10, 0), (4, 10, 2), (4, 10, 1), (2, 12, 0), (2, 12, 1), (3, 10, 0), (3, 10, 2), (5, 9, 1), (5, 9, 2), (0, 14, 2), (0, 14, 0)]

private def codeBlock10 : Fin 16 → Code :=
  ![(2, 13, 2), (2, 13, 1), (3, 11, 1), (3, 11, 2), (4, 11, 0), (4, 11, 1), (5, 10, 0), (5, 10, 2), (1, 13, 2), (1, 13, 0), (2, 14, 0), (2, 14, 1), (3, 12, 0), (3, 12, 2), (4, 12, 2), (4, 12, 1)]

private def codeBlock11 : Fin 16 → Code :=
  ![(5, 11, 1), (5, 11, 2), (0, 15, 0), (1, 14, 0), (2, 15, 1), (3, 13, 2), (4, 13, 1), (5, 12, 2), (0, 16, 2), (1, 15, 1), (2, 16, 2), (3, 14, 1), (4, 14, 0), (5, 13, 0), (0, 17, 2), (0, 17, 1)]

private def codeBlock12 : Fin 16 → Code :=
  ![(1, 16, 1), (1, 16, 2), (2, 17, 2), (2, 17, 0), (3, 15, 1), (3, 15, 0), (4, 15, 0), (4, 15, 2), (0, 18, 2), (0, 18, 1), (2, 18, 2), (2, 18, 0), (3, 16, 1), (3, 16, 0), (1, 17, 1), (1, 17, 2)]

private def codeBlock13 : Fin 16 → Code :=
  ![(4, 16, 0), (4, 16, 2), (5, 14, 0), (5, 14, 1), (1, 18, 1), (1, 18, 2), (4, 17, 0), (4, 17, 2), (5, 15, 0), (5, 15, 1), (0, 19, 1), (1, 19, 2), (2, 19, 0), (3, 17, 0), (4, 18, 2), (5, 16, 1)]

private def codeBlock14 : Fin 16 → Code :=
  ![(0, 20, 2), (0, 20, 0), (1, 20, 1), (1, 20, 0), (2, 20, 2), (2, 20, 1), (3, 18, 1), (3, 18, 2), (5, 17, 0), (5, 17, 2), (0, 21, 2), (0, 21, 1), (0, 21, 0), (1, 21, 1), (1, 21, 2), (1, 21, 0)]

private def codeBlock15 : Fin 16 → Code :=
  ![(2, 21, 2), (2, 21, 0), (2, 21, 1), (3, 19, 1), (3, 19, 0), (3, 19, 2), (4, 19, 0), (4, 19, 2), (4, 19, 1), (5, 18, 0), (5, 18, 1), (5, 18, 2), (2, 22, 2), (2, 22, 0), (2, 22, 1), (3, 20, 1)]

private def codeBlock16 : Fin 16 → Code :=
  ![(3, 20, 0), (3, 20, 2), (4, 20, 0), (4, 20, 2), (4, 20, 1), (5, 19, 0), (5, 19, 1), (5, 19, 2), (0, 22, 2), (0, 22, 1), (0, 22, 0), (1, 22, 1), (1, 22, 2), (1, 22, 0), (4, 21, 0), (4, 21, 2)]

private def codeBlock17 : Fin 16 → Code :=
  ![(4, 21, 1), (5, 20, 0), (5, 20, 1), (5, 20, 2), (0, 23, 1), (0, 23, 0), (1, 23, 2), (1, 23, 0), (4, 22, 2), (4, 22, 1), (0, 24, 2), (0, 24, 0), (1, 24, 1), (1, 24, 0), (2, 23, 2), (2, 23, 1)]

private def codeBlock18 : Fin 16 → Code :=
  ![(0, 25, 2), (0, 25, 1), (0, 25, 0), (1, 25, 1), (1, 25, 2), (1, 25, 0), (4, 23, 0), (4, 23, 2), (4, 23, 1), (5, 21, 0), (5, 21, 1), (5, 21, 2), (0, 26, 2), (0, 26, 1), (0, 26, 0), (1, 26, 1)]

private def codeBlock19 : Fin 16 → Code :=
  ![(1, 26, 2), (1, 26, 0), (2, 24, 2), (2, 24, 0), (2, 24, 1), (3, 21, 1), (3, 21, 0), (3, 21, 2), (0, 27, 1), (0, 27, 0), (1, 27, 2), (1, 27, 0), (4, 24, 2), (4, 24, 1), (3, 22, 1), (3, 22, 2)]

private def codeBlock20 : Fin 16 → Code :=
  ![(4, 25, 0), (4, 25, 1), (5, 22, 0), (5, 22, 2), (0, 28, 2), (0, 28, 1), (0, 28, 0), (1, 28, 1), (1, 28, 2), (1, 28, 0), (2, 25, 2), (2, 25, 0), (2, 25, 1), (4, 26, 0), (4, 26, 2), (4, 26, 1)]

private def codeBlock21 : Fin 16 → Code :=
  ![(2, 26, 0), (2, 26, 1), (3, 23, 0), (3, 23, 2), (5, 23, 1), (5, 23, 2), (0, 29, 2), (0, 29, 0), (2, 27, 2), (2, 27, 1), (3, 24, 1), (3, 24, 2), (4, 27, 0), (4, 27, 1), (5, 24, 0), (5, 24, 2)]

private def codeBlock22 : Fin 16 → Code :=
  ![(1, 29, 2), (1, 29, 0), (2, 28, 0), (2, 28, 1), (3, 25, 0), (3, 25, 2), (4, 28, 2), (4, 28, 1), (5, 25, 1), (5, 25, 2), (0, 30, 0), (1, 30, 0), (2, 29, 1), (3, 26, 2), (4, 29, 1), (5, 26, 2)]

private def codeBlock23 : Fin 16 → Code :=
  ![(0, 31, 2), (1, 31, 1), (2, 30, 2), (3, 27, 1), (4, 30, 0), (5, 27, 0), (0, 32, 2), (0, 32, 1), (2, 31, 2), (2, 31, 0), (3, 28, 1), (3, 28, 0), (0, 33, 2), (0, 33, 1), (2, 32, 2), (2, 32, 0)]

private def codeBlock24 : Fin 16 → Code :=
  ![(3, 29, 1), (3, 29, 0), (1, 32, 1), (1, 32, 2), (4, 31, 0), (4, 31, 2), (5, 28, 0), (5, 28, 1), (0, 34, 2), (0, 34, 1), (1, 33, 1), (1, 33, 2), (2, 33, 2), (2, 33, 0), (4, 32, 0), (4, 32, 2)]

private def codeBlock25 : Fin 16 → Code :=
  ![(5, 29, 0), (5, 29, 1), (0, 35, 1), (1, 34, 2), (2, 34, 0), (3, 30, 0), (4, 33, 2), (5, 30, 1), (0, 36, 2), (0, 36, 0), (1, 35, 1), (1, 35, 0), (2, 35, 2), (2, 35, 1), (0, 37, 2), (0, 37, 1)]

private def codeBlock26 : Fin 16 → Code :=
  ![(0, 37, 0), (1, 36, 1), (1, 36, 2), (1, 36, 0), (2, 36, 2), (2, 36, 0), (2, 36, 1), (3, 31, 1), (3, 31, 0), (3, 31, 2), (2, 37, 2), (2, 37, 0), (2, 37, 1), (3, 32, 1), (3, 32, 0), (3, 32, 2)]

private def codeBlock27 : Fin 16 → Code :=
  ![(4, 34, 0), (4, 34, 2), (4, 34, 1), (5, 31, 0), (5, 31, 1), (5, 31, 2), (0, 38, 2), (0, 38, 1), (0, 38, 0), (2, 38, 2), (2, 38, 0), (2, 38, 1), (3, 33, 1), (3, 33, 0), (3, 33, 2), (5, 32, 0)]

private def codeBlock28 : Fin 16 → Code :=
  ![(5, 32, 1), (5, 32, 2), (0, 39, 1), (0, 39, 0), (1, 37, 2), (1, 37, 0), (3, 34, 0), (3, 34, 2), (4, 35, 2), (4, 35, 1), (5, 33, 1), (5, 33, 2), (0, 40, 2), (0, 40, 0), (1, 38, 1), (1, 38, 0)]

private def codeBlock29 : Fin 16 → Code :=
  ![(2, 39, 2), (2, 39, 1), (0, 41, 2), (0, 41, 1), (0, 41, 0), (1, 39, 1), (1, 39, 2), (1, 39, 0), (4, 36, 0), (4, 36, 2), (4, 36, 1), (5, 34, 0), (5, 34, 1), (5, 34, 2), (0, 42, 2), (0, 42, 1)]

private def codeBlock30 : Fin 16 → Code :=
  ![(0, 42, 0), (1, 40, 1), (1, 40, 2), (1, 40, 0), (2, 40, 2), (2, 40, 0), (2, 40, 1), (3, 35, 1), (3, 35, 0), (3, 35, 2), (0, 43, 1), (0, 43, 0), (1, 41, 2), (1, 41, 0), (4, 37, 2), (4, 37, 1)]

private def codeBlock31 : Fin 16 → Code :=
  ![(3, 36, 1), (3, 36, 2), (4, 38, 0), (4, 38, 1), (5, 35, 0), (5, 35, 2), (0, 44, 2), (0, 44, 1), (0, 44, 0), (1, 42, 1), (1, 42, 2), (1, 42, 0), (2, 41, 2), (2, 41, 0), (2, 41, 1), (3, 37, 1)]

private def codeBlock32 : Fin 16 → Code :=
  ![(3, 37, 0), (3, 37, 2), (4, 39, 0), (4, 39, 2), (4, 39, 1), (5, 36, 0), (5, 36, 1), (5, 36, 2), (2, 42, 0), (2, 42, 1), (3, 38, 0), (3, 38, 2), (5, 37, 1), (5, 37, 2), (0, 45, 2), (0, 45, 0)]

private def codeBlock33 : Fin 16 → Code :=
  ![(2, 43, 2), (2, 43, 1), (3, 39, 1), (3, 39, 2), (4, 40, 0), (4, 40, 1), (5, 38, 0), (5, 38, 2), (1, 43, 2), (1, 43, 0), (2, 44, 0), (2, 44, 1), (3, 40, 0), (3, 40, 2), (4, 41, 2), (4, 41, 1)]

private def codeBlock34 : Fin 16 → Code :=
  ![(5, 39, 1), (5, 39, 2), (0, 46, 0), (1, 44, 0), (2, 45, 1), (3, 41, 2), (4, 42, 1), (5, 40, 2), (0, 47, 2), (1, 45, 1), (2, 46, 2), (3, 42, 1), (4, 43, 0), (5, 41, 0), (0, 48, 2), (0, 48, 1)]

private def codeBlock35 : Fin 16 → Code :=
  ![(1, 46, 1), (1, 46, 2), (2, 47, 2), (2, 47, 0), (3, 43, 1), (3, 43, 0), (4, 44, 0), (4, 44, 2), (0, 49, 2), (0, 49, 1), (2, 48, 2), (2, 48, 0), (3, 44, 1), (3, 44, 0), (1, 47, 1), (1, 47, 2)]

private def codeBlock36 : Fin 16 → Code :=
  ![(4, 45, 0), (4, 45, 2), (5, 42, 0), (5, 42, 1), (0, 50, 2), (0, 50, 1), (1, 48, 1), (1, 48, 2), (2, 49, 2), (2, 49, 0), (4, 46, 0), (4, 46, 2), (5, 43, 0), (5, 43, 1), (0, 51, 1), (1, 49, 2)]

private def codeBlock37 : Fin 16 → Code :=
  ![(2, 50, 0), (3, 45, 0), (4, 47, 2), (5, 44, 1), (0, 52, 2), (0, 52, 0), (1, 50, 1), (1, 50, 0), (2, 51, 2), (2, 51, 1), (3, 46, 1), (3, 46, 2), (5, 45, 0), (5, 45, 2), (0, 53, 2), (0, 53, 1)]

private def codeBlock38 : Fin 16 → Code :=
  ![(0, 53, 0), (1, 51, 1), (1, 51, 2), (1, 51, 0), (2, 52, 2), (2, 52, 0), (2, 52, 1), (3, 47, 1), (3, 47, 0), (3, 47, 2), (4, 48, 0), (4, 48, 2), (4, 48, 1), (5, 46, 0), (5, 46, 1), (5, 46, 2)]

private def codeBlock39 : Fin 16 → Code :=
  ![(2, 53, 2), (2, 53, 0), (2, 53, 1), (3, 48, 1), (3, 48, 0), (3, 48, 2), (4, 49, 0), (4, 49, 2), (4, 49, 1), (5, 47, 0), (5, 47, 1), (5, 47, 2), (0, 54, 2), (0, 54, 1), (0, 54, 0), (2, 54, 2)]

private def codeBlock40 : Fin 16 → Code :=
  ![(2, 54, 0), (2, 54, 1), (3, 49, 1), (3, 49, 0), (3, 49, 2), (5, 48, 0), (5, 48, 1), (5, 48, 2), (0, 55, 1), (0, 55, 0), (1, 52, 2), (1, 52, 0), (3, 50, 0), (3, 50, 2), (4, 50, 2), (4, 50, 1)]

private def codeBlock41 : Fin 16 → Code :=
  ![(5, 49, 1), (5, 49, 2), (0, 56, 2), (0, 56, 0), (1, 53, 1), (1, 53, 0), (2, 55, 2), (2, 55, 1), (0, 57, 2), (0, 57, 1), (0, 57, 0), (1, 54, 1), (1, 54, 2), (1, 54, 0), (4, 51, 0), (4, 51, 2)]

private def codeBlock42 : Fin 16 → Code :=
  ![(4, 51, 1), (5, 50, 0), (5, 50, 1), (5, 50, 2), (0, 58, 2), (0, 58, 1), (0, 58, 0), (1, 55, 1), (1, 55, 2), (1, 55, 0), (2, 56, 2), (2, 56, 0), (2, 56, 1), (3, 51, 1), (3, 51, 0), (3, 51, 2)]

private def codeBlock43 : Fin 16 → Code :=
  ![(0, 59, 1), (0, 59, 0), (1, 56, 2), (1, 56, 0), (4, 52, 2), (4, 52, 1), (3, 52, 1), (3, 52, 2), (4, 53, 0), (4, 53, 1), (5, 51, 0), (5, 51, 2), (2, 57, 2), (2, 57, 0), (2, 57, 1), (3, 53, 1)]

private def codeBlock44 : Fin 16 → Code :=
  ![(3, 53, 0), (3, 53, 2), (4, 54, 0), (4, 54, 2), (4, 54, 1), (5, 52, 0), (5, 52, 1), (5, 52, 2), (2, 58, 0), (2, 58, 1), (3, 54, 0), (3, 54, 2), (5, 53, 1), (5, 53, 2), (3, 55, 1), (3, 55, 2)]

private def codeBlock45 : Fin 16 → Code :=
  ![(4, 55, 0), (4, 55, 1), (5, 54, 0), (5, 54, 2), (2, 59, 0), (2, 59, 1), (3, 56, 0), (3, 56, 2), (5, 55, 1), (5, 55, 2), (0, 60, 0), (1, 57, 0), (2, 60, 1), (3, 57, 2), (4, 56, 1), (5, 56, 2)]

private def codeBlock46 : Fin 16 → Code :=
  ![(0, 61, 2), (1, 58, 1), (2, 61, 2), (3, 58, 1), (4, 57, 0), (5, 57, 0), (0, 62, 2), (0, 62, 1), (1, 59, 1), (1, 59, 2), (2, 62, 2), (2, 62, 0), (3, 59, 1), (3, 59, 0), (4, 58, 0), (4, 58, 2)]

private def codeBlock47 : Fin 16 → Code :=
  ![(0, 63, 2), (0, 63, 1), (2, 63, 2), (2, 63, 0), (3, 60, 1), (3, 60, 0), (1, 60, 1), (1, 60, 2), (4, 59, 0), (4, 59, 2), (5, 58, 0), (5, 58, 1), (1, 61, 1), (1, 61, 2), (4, 60, 0), (4, 60, 2)]

private def codeBlock48 : Fin 16 → Code :=
  ![(5, 59, 0), (5, 59, 1), (0, 64, 1), (1, 62, 2), (2, 64, 0), (3, 61, 0), (4, 61, 2), (5, 60, 1), (0, 65, 2), (0, 65, 0), (1, 63, 1), (1, 63, 0), (2, 65, 2), (2, 65, 1), (3, 62, 1), (3, 62, 2)]

private def codeBlock49 : Fin 16 → Code :=
  ![(5, 61, 0), (5, 61, 2), (1, 64, 1), (1, 64, 2), (1, 64, 0), (3, 63, 1), (3, 63, 0), (3, 63, 2), (4, 62, 0), (4, 62, 2), (4, 62, 1), (5, 62, 0), (5, 62, 1), (5, 62, 2), (2, 66, 2), (2, 66, 0)]

private def codeBlock50 : Fin 16 → Code :=
  ![(2, 66, 1), (3, 64, 1), (3, 64, 0), (3, 64, 2), (4, 63, 0), (4, 63, 2), (4, 63, 1), (5, 63, 0), (5, 63, 1), (5, 63, 2), (0, 66, 2), (0, 66, 1), (0, 66, 0), (1, 65, 1), (1, 65, 2), (1, 65, 0)]

private def codeBlock51 : Fin 16 → Code :=
  ![(4, 64, 0), (4, 64, 2), (4, 64, 1), (5, 64, 0), (5, 64, 1), (5, 64, 2), (0, 67, 1), (0, 67, 0), (1, 66, 2), (1, 66, 0), (4, 65, 2), (4, 65, 1), (0, 68, 2), (0, 68, 0), (1, 67, 1), (1, 67, 0)]

private def codeBlock52 : Fin 16 → Code :=
  ![(2, 67, 2), (2, 67, 1), (0, 69, 2), (0, 69, 1), (0, 69, 0), (1, 68, 1), (1, 68, 2), (1, 68, 0), (4, 66, 0), (4, 66, 2), (4, 66, 1), (5, 65, 0), (5, 65, 1), (5, 65, 2), (0, 70, 2), (0, 70, 1)]

private def codeBlock53 : Fin 16 → Code :=
  ![(0, 70, 0), (1, 69, 1), (1, 69, 2), (1, 69, 0), (2, 68, 2), (2, 68, 0), (2, 68, 1), (3, 65, 1), (3, 65, 0), (3, 65, 2), (0, 71, 1), (0, 71, 0), (1, 70, 2), (1, 70, 0), (4, 67, 2), (4, 67, 1)]

private def codeBlock54 : Fin 16 → Code :=
  ![(3, 66, 1), (3, 66, 2), (4, 68, 0), (4, 68, 1), (5, 66, 0), (5, 66, 2), (0, 72, 2), (0, 72, 1), (0, 72, 0), (1, 71, 1), (1, 71, 2), (1, 71, 0), (2, 69, 2), (2, 69, 0), (2, 69, 1), (3, 67, 1)]

private def codeBlock55 : Fin 16 → Code :=
  ![(3, 67, 0), (3, 67, 2), (4, 69, 0), (4, 69, 2), (4, 69, 1), (5, 67, 0), (5, 67, 1), (5, 67, 2), (2, 70, 0), (2, 70, 1), (3, 68, 0), (3, 68, 2), (5, 68, 1), (5, 68, 2), (0, 73, 2), (0, 73, 0)]

private def codeBlock56 : Fin 16 → Code :=
  ![(2, 71, 2), (2, 71, 1), (3, 69, 1), (3, 69, 2), (4, 70, 0), (4, 70, 1), (5, 69, 0), (5, 69, 2), (1, 72, 2), (1, 72, 0), (2, 72, 0), (2, 72, 1), (3, 70, 0), (3, 70, 2), (4, 71, 2), (4, 71, 1)]

private def codeBlock57 : Fin 16 → Code :=
  ![(5, 70, 1), (5, 70, 2), (0, 74, 0), (1, 73, 0), (2, 73, 1), (3, 71, 2), (4, 72, 1), (5, 71, 2), (0, 75, 2), (1, 74, 1), (2, 74, 2), (3, 72, 1), (4, 73, 0), (5, 72, 0), (0, 76, 2), (0, 76, 1)]

private def codeBlock58 : Fin 16 → Code :=
  ![(1, 75, 1), (1, 75, 2), (2, 75, 2), (2, 75, 0), (3, 73, 1), (3, 73, 0), (4, 74, 0), (4, 74, 2), (0, 77, 2), (0, 77, 1), (2, 76, 2), (2, 76, 0), (3, 74, 1), (3, 74, 0), (1, 76, 1), (1, 76, 2)]

private def codeBlock59 : Fin 16 → Code :=
  ![(4, 75, 0), (4, 75, 2), (5, 73, 0), (5, 73, 1), (0, 78, 2), (0, 78, 1), (1, 77, 1), (1, 77, 2), (2, 77, 2), (2, 77, 0), (4, 76, 0), (4, 76, 2), (5, 74, 0), (5, 74, 1), (0, 79, 1), (1, 78, 2)]

private def codeBlock60 : Fin 16 → Code :=
  ![(2, 78, 0), (3, 75, 0), (4, 77, 2), (5, 75, 1), (0, 80, 2), (0, 80, 0), (1, 79, 1), (1, 79, 0), (2, 79, 2), (2, 79, 1), (3, 76, 1), (3, 76, 2), (5, 76, 0), (5, 76, 2), (1, 80, 1), (1, 80, 2)]

private def codeBlock61 : Fin 16 → Code :=
  ![(1, 80, 0), (3, 77, 1), (3, 77, 0), (3, 77, 2), (4, 78, 0), (4, 78, 2), (4, 78, 1), (5, 77, 0), (5, 77, 1), (5, 77, 2), (2, 80, 2), (2, 80, 0), (2, 80, 1), (3, 78, 1), (3, 78, 0), (3, 78, 2)]

private def codeBlock62 : Fin 16 → Code :=
  ![(4, 79, 0), (4, 79, 2), (4, 79, 1), (5, 78, 0), (5, 78, 1), (5, 78, 2), (0, 81, 2), (0, 81, 1), (0, 81, 0), (1, 81, 1), (1, 81, 2), (1, 81, 0), (2, 81, 2), (2, 81, 0), (2, 81, 1), (3, 79, 1)]

private def codeBlock63 : Fin 16 → Code :=
  ![(3, 79, 0), (3, 79, 2), (4, 80, 0), (4, 80, 2), (4, 80, 1), (5, 79, 0), (5, 79, 1), (5, 79, 2), (0, 82, 1), (0, 82, 0), (1, 82, 2), (1, 82, 0), (3, 80, 0), (3, 80, 2), (4, 81, 2), (4, 81, 1)]

private def codeBlock64 : Fin 16 → Code :=
  ![(5, 80, 1), (5, 80, 2), (0, 83, 2), (0, 83, 0), (1, 83, 1), (1, 83, 0), (2, 82, 2), (2, 82, 1), (0, 84, 2), (0, 84, 1), (0, 84, 0), (1, 84, 1), (1, 84, 2), (1, 84, 0), (4, 82, 0), (4, 82, 2)]

private def codeBlock65 : Fin 16 → Code :=
  ![(4, 82, 1), (5, 81, 0), (5, 81, 1), (5, 81, 2), (0, 85, 2), (0, 85, 1), (0, 85, 0), (1, 85, 1), (1, 85, 2), (1, 85, 0), (2, 83, 2), (2, 83, 0), (2, 83, 1), (3, 81, 1), (3, 81, 0), (3, 81, 2)]

private def codeBlock66 : Fin 16 → Code :=
  ![(0, 86, 1), (0, 86, 0), (1, 86, 2), (1, 86, 0), (4, 83, 2), (4, 83, 1), (3, 82, 1), (3, 82, 2), (4, 84, 0), (4, 84, 1), (5, 82, 0), (5, 82, 2), (2, 84, 2), (2, 84, 0), (2, 84, 1), (3, 83, 1)]

private def codeBlock67 : Fin 16 → Code :=
  ![(3, 83, 0), (3, 83, 2), (4, 85, 0), (4, 85, 2), (4, 85, 1), (5, 83, 0), (5, 83, 1), (5, 83, 2), (2, 85, 0), (2, 85, 1), (3, 84, 0), (3, 84, 2), (5, 84, 1), (5, 84, 2), (3, 85, 1), (3, 85, 2)]

private def codeBlock68 : Fin 16 → Code :=
  ![(4, 86, 0), (4, 86, 1), (5, 85, 0), (5, 85, 2), (2, 86, 0), (2, 86, 1), (3, 86, 0), (3, 86, 2), (5, 86, 1), (5, 86, 2), (0, 87, 0), (1, 87, 0), (2, 87, 1), (3, 87, 2), (4, 87, 1), (5, 87, 2)]

private def codeTable : Fin 69 → Fin 16 → Code :=
  ![codeBlock0, codeBlock1, codeBlock2, codeBlock3, codeBlock4, codeBlock5, codeBlock6, codeBlock7, codeBlock8, codeBlock9, codeBlock10, codeBlock11, codeBlock12, codeBlock13, codeBlock14, codeBlock15, codeBlock16, codeBlock17, codeBlock18, codeBlock19, codeBlock20, codeBlock21, codeBlock22, codeBlock23, codeBlock24, codeBlock25, codeBlock26, codeBlock27, codeBlock28, codeBlock29, codeBlock30, codeBlock31, codeBlock32, codeBlock33, codeBlock34, codeBlock35, codeBlock36, codeBlock37, codeBlock38, codeBlock39, codeBlock40, codeBlock41, codeBlock42, codeBlock43, codeBlock44, codeBlock45, codeBlock46, codeBlock47, codeBlock48, codeBlock49, codeBlock50, codeBlock51, codeBlock52, codeBlock53, codeBlock54, codeBlock55, codeBlock56, codeBlock57, codeBlock58, codeBlock59, codeBlock60, codeBlock61, codeBlock62, codeBlock63, codeBlock64, codeBlock65, codeBlock66, codeBlock67, codeBlock68]

private def forwardCode (row : Fin 1104) : Code :=
  codeTable (rowBlock row) (rowOffset row)

private def inverseRegion0 : Fin 88 → Fin 3 → Fin 1104 :=
  ![![0, 0, 0], ![0, 7, 6], ![0, 13, 12], ![0, 25, 24], ![0, 34, 0], ![41, 0, 40], ![48, 47, 46], ![72, 71, 70], ![89, 88, 0], ![99, 0, 98], ![106, 105, 104], ![118, 117, 116], ![129, 128, 0], ![142, 141, 140], ![159, 0, 158], ![178, 0, 0], ![0, 0, 184], ![0, 191, 190], ![0, 201, 200], ![0, 218, 0], ![225, 0, 224], ![236, 235, 234], ![266, 265, 264], ![277, 276, 0], ![283, 0, 282], ![290, 289, 288], ![302, 301, 300], ![313, 312, 0], ![326, 325, 324], ![343, 0, 342], ![362, 0, 0], ![0, 0, 368], ![0, 375, 374], ![0, 381, 380], ![0, 393, 392], ![0, 402, 0], ![409, 0, 408], ![416, 415, 414], ![440, 439, 438], ![451, 450, 0], ![461, 0, 460], ![468, 467, 466], ![480, 479, 478], ![491, 490, 0], ![504, 503, 502], ![527, 0, 526], ![546, 0, 0], ![0, 0, 552], ![0, 559, 558], ![0, 569, 568], ![0, 581, 580], ![0, 590, 0], ![597, 0, 596], ![608, 607, 606], ![638, 637, 636], ![649, 648, 0], ![659, 0, 658], ![666, 665, 664], ![678, 677, 676], ![689, 688, 0], ![730, 0, 0], ![0, 0, 736], ![0, 743, 742], ![0, 753, 752], ![0, 770, 0], ![777, 0, 776], ![812, 811, 810], ![823, 822, 0], ![829, 0, 828], ![836, 835, 834], ![848, 847, 846], ![859, 858, 0], ![872, 871, 870], ![895, 0, 894], ![914, 0, 0], ![0, 0, 920], ![0, 927, 926], ![0, 937, 936], ![0, 949, 948], ![0, 958, 0], ![965, 0, 964], ![1000, 999, 998], ![1017, 1016, 0], ![1027, 0, 1026], ![1034, 1033, 1032], ![1046, 1045, 1044], ![1057, 1056, 0], ![1098, 0, 0]]

private def inverseRegion1 : Fin 88 → Fin 3 → Fin 1104 :=
  ![![0, 1, 0], ![0, 18, 19], ![0, 26, 27], ![0, 0, 35], ![43, 42, 0], ![51, 49, 50], ![75, 73, 74], ![91, 0, 90], ![101, 100, 0], ![109, 107, 108], ![121, 119, 120], ![131, 0, 130], ![145, 143, 144], ![169, 0, 168], ![179, 0, 0], ![0, 185, 0], ![0, 192, 193], ![0, 206, 207], ![0, 212, 213], ![0, 0, 219], ![227, 226, 0], ![239, 237, 238], ![269, 267, 268], ![279, 0, 278], ![285, 284, 0], ![293, 291, 292], ![305, 303, 304], ![315, 0, 314], ![329, 327, 328], ![353, 0, 352], ![363, 0, 0], ![0, 369, 0], ![0, 386, 387], ![0, 394, 395], ![0, 0, 403], ![411, 410, 0], ![419, 417, 418], ![453, 0, 452], ![463, 462, 0], ![471, 469, 470], ![483, 481, 482], ![493, 0, 492], ![507, 505, 506], ![537, 0, 536], ![547, 0, 0], ![0, 553, 0], ![0, 560, 561], ![0, 574, 575], ![0, 582, 583], ![0, 0, 591], ![599, 598, 0], ![611, 609, 610], ![651, 0, 650], ![661, 660, 0], ![669, 667, 668], ![681, 679, 680], ![691, 0, 690], ![731, 0, 0], ![0, 737, 0], ![0, 744, 745], ![0, 758, 759], ![0, 764, 765], ![0, 0, 771], ![779, 778, 0], ![788, 786, 787], ![815, 813, 814], ![825, 0, 824], ![831, 830, 0], ![839, 837, 838], ![851, 849, 850], ![861, 0, 860], ![875, 873, 874], ![905, 0, 904], ![915, 0, 0], ![0, 921, 0], ![0, 928, 929], ![0, 942, 943], ![0, 950, 951], ![0, 0, 959], ![967, 966, 0], ![976, 974, 975], ![1003, 1001, 1002], ![1019, 0, 1018], ![1029, 1028, 0], ![1037, 1035, 1036], ![1049, 1047, 1048], ![1059, 0, 1058], ![1099, 0, 0]]

private def inverseRegion2 : Fin 88 → Fin 3 → Fin 1104 :=
  ![![0, 0, 2], ![9, 0, 8], ![15, 0, 14], ![29, 0, 28], ![36, 0, 0], ![0, 45, 44], ![53, 54, 52], ![59, 60, 58], ![77, 78, 76], ![0, 103, 102], ![123, 124, 122], ![147, 148, 146], ![152, 153, 0], ![0, 161, 160], ![170, 171, 0], ![0, 180, 0], ![0, 0, 186], ![195, 0, 194], ![203, 0, 202], ![220, 0, 0], ![0, 229, 228], ![241, 242, 240], ![253, 254, 252], ![0, 287, 286], ![307, 308, 306], ![331, 332, 330], ![336, 337, 0], ![0, 345, 344], ![354, 355, 0], ![0, 364, 0], ![0, 0, 370], ![377, 0, 376], ![383, 0, 382], ![397, 0, 396], ![404, 0, 0], ![0, 413, 412], ![421, 422, 420], ![427, 428, 426], ![442, 443, 441], ![0, 465, 464], ![485, 486, 484], ![509, 510, 508], ![520, 521, 0], ![0, 529, 528], ![538, 539, 0], ![0, 548, 0], ![0, 0, 554], ![563, 0, 562], ![571, 0, 570], ![585, 0, 584], ![592, 0, 0], ![0, 601, 600], ![613, 614, 612], ![625, 626, 624], ![640, 641, 639], ![0, 663, 662], ![683, 684, 682], ![701, 702, 700], ![712, 713, 0], ![724, 725, 0], ![0, 732, 0], ![0, 0, 738], ![747, 0, 746], ![755, 0, 754], ![772, 0, 0], ![0, 781, 780], ![799, 800, 798], ![0, 833, 832], ![853, 854, 852], ![877, 878, 876], ![888, 889, 0], ![0, 897, 896], ![906, 907, 0], ![0, 916, 0], ![0, 0, 922], ![931, 0, 930], ![939, 0, 938], ![953, 0, 952], ![960, 0, 0], ![0, 969, 968], ![987, 988, 986], ![1005, 1006, 1004], ![0, 1031, 1030], ![1051, 1052, 1050], ![1069, 1070, 1068], ![1080, 1081, 0], ![1092, 1093, 0], ![0, 1100, 0]]

private def inverseRegion3 : Fin 88 → Fin 3 → Fin 1104 :=
  ![![0, 3, 0], ![11, 10, 0], ![17, 16, 0], ![37, 0, 0], ![56, 55, 57], ![62, 61, 63], ![80, 79, 81], ![92, 0, 93], ![126, 125, 127], ![0, 134, 135], ![154, 0, 155], ![0, 162, 163], ![172, 0, 173], ![0, 0, 181], ![0, 187, 0], ![197, 196, 0], ![205, 204, 0], ![221, 0, 0], ![0, 230, 231], ![244, 243, 245], ![256, 255, 257], ![310, 309, 311], ![0, 318, 319], ![338, 0, 339], ![0, 346, 347], ![356, 0, 357], ![0, 0, 365], ![0, 371, 0], ![379, 378, 0], ![385, 384, 0], ![405, 0, 0], ![424, 423, 425], ![430, 429, 431], ![445, 444, 446], ![454, 0, 455], ![488, 487, 489], ![0, 496, 497], ![512, 511, 513], ![522, 0, 523], ![0, 530, 531], ![540, 0, 541], ![0, 0, 549], ![0, 555, 0], ![565, 564, 0], ![573, 572, 0], ![593, 0, 0], ![0, 602, 603], ![616, 615, 617], ![628, 627, 629], ![643, 642, 644], ![652, 0, 653], ![686, 685, 687], ![0, 694, 695], ![704, 703, 705], ![714, 0, 715], ![0, 718, 719], ![726, 0, 727], ![0, 0, 733], ![0, 739, 0], ![749, 748, 0], ![757, 756, 0], ![773, 0, 0], ![0, 782, 783], ![790, 789, 791], ![802, 801, 803], ![856, 855, 857], ![0, 864, 865], ![880, 879, 881], ![890, 0, 891], ![0, 898, 899], ![908, 0, 909], ![0, 0, 917], ![0, 923, 0], ![933, 932, 0], ![941, 940, 0], ![961, 0, 0], ![0, 970, 971], ![978, 977, 979], ![990, 989, 991], ![1008, 1007, 1009], ![1020, 0, 1021], ![1054, 1053, 1055], ![0, 1062, 1063], ![1072, 1071, 1073], ![1082, 0, 1083], ![0, 1086, 1087], ![1094, 0, 1095], ![0, 0, 1101]]

private def inverseRegion4 : Fin 88 → Fin 3 → Fin 1104 :=
  ![![4, 0, 0], ![20, 0, 21], ![30, 0, 31], ![0, 0, 38], ![64, 66, 65], ![82, 84, 83], ![0, 95, 94], ![110, 112, 111], ![0, 133, 132], ![136, 137, 0], ![149, 151, 150], ![164, 165, 0], ![0, 175, 174], ![0, 182, 0], ![188, 0, 0], ![198, 0, 199], ![208, 0, 209], ![214, 0, 215], ![0, 0, 222], ![246, 248, 247], ![258, 260, 259], ![270, 272, 271], ![0, 281, 280], ![294, 296, 295], ![0, 317, 316], ![320, 321, 0], ![333, 335, 334], ![348, 349, 0], ![0, 359, 358], ![0, 366, 0], ![372, 0, 0], ![388, 0, 389], ![398, 0, 399], ![0, 0, 406], ![432, 434, 433], ![0, 457, 456], ![472, 474, 473], ![0, 495, 494], ![498, 499, 0], ![514, 516, 515], ![532, 533, 0], ![0, 543, 542], ![0, 550, 0], ![556, 0, 0], ![566, 0, 567], ![576, 0, 577], ![586, 0, 587], ![0, 0, 594], ![618, 620, 619], ![630, 632, 631], ![0, 655, 654], ![670, 672, 671], ![0, 693, 692], ![696, 697, 0], ![706, 708, 707], ![720, 721, 0], ![0, 734, 0], ![740, 0, 0], ![750, 0, 751], ![760, 0, 761], ![766, 0, 767], ![0, 0, 774], ![792, 794, 793], ![804, 806, 805], ![816, 818, 817], ![0, 827, 826], ![840, 842, 841], ![0, 863, 862], ![866, 867, 0], ![882, 884, 883], ![900, 901, 0], ![0, 911, 910], ![0, 918, 0], ![924, 0, 0], ![934, 0, 935], ![944, 0, 945], ![954, 0, 955], ![0, 0, 962], ![980, 982, 981], ![992, 994, 993], ![1010, 1012, 1011], ![0, 1023, 1022], ![1038, 1040, 1039], ![0, 1061, 1060], ![1064, 1065, 0], ![1074, 1076, 1075], ![1088, 1089, 0], ![0, 1102, 0]]

private def inverseRegion5 : Fin 88 → Fin 3 → Fin 1104 :=
  ![![5, 0, 0], ![22, 23, 0], ![32, 33, 0], ![0, 39, 0], ![67, 68, 69], ![85, 86, 87], ![0, 96, 97], ![113, 114, 115], ![138, 0, 139], ![0, 156, 157], ![166, 0, 167], ![0, 176, 177], ![0, 0, 183], ![189, 0, 0], ![210, 211, 0], ![216, 217, 0], ![0, 223, 0], ![232, 0, 233], ![249, 250, 251], ![261, 262, 263], ![273, 274, 275], ![297, 298, 299], ![322, 0, 323], ![0, 340, 341], ![350, 0, 351], ![0, 360, 361], ![0, 0, 367], ![373, 0, 0], ![390, 391, 0], ![400, 401, 0], ![0, 407, 0], ![435, 436, 437], ![447, 448, 449], ![0, 458, 459], ![475, 476, 477], ![500, 0, 501], ![517, 518, 519], ![0, 524, 525], ![534, 0, 535], ![0, 544, 545], ![0, 0, 551], ![557, 0, 0], ![578, 579, 0], ![588, 589, 0], ![0, 595, 0], ![604, 0, 605], ![621, 622, 623], ![633, 634, 635], ![645, 646, 647], ![0, 656, 657], ![673, 674, 675], ![698, 0, 699], ![709, 710, 711], ![0, 716, 717], ![722, 0, 723], ![0, 728, 729], ![0, 0, 735], ![741, 0, 0], ![762, 763, 0], ![768, 769, 0], ![0, 775, 0], ![784, 0, 785], ![795, 796, 797], ![807, 808, 809], ![819, 820, 821], ![843, 844, 845], ![868, 0, 869], ![885, 886, 887], ![0, 892, 893], ![902, 0, 903], ![0, 912, 913], ![0, 0, 919], ![925, 0, 0], ![946, 947, 0], ![956, 957, 0], ![0, 963, 0], ![972, 0, 973], ![983, 984, 985], ![995, 996, 997], ![1013, 1014, 1015], ![0, 1024, 1025], ![1041, 1042, 1043], ![1066, 0, 1067], ![1077, 1078, 1079], ![0, 1084, 1085], ![1090, 0, 1091], ![0, 1096, 1097], ![0, 0, 1103]]

private def inverseTable : Fin 6 → Fin 88 → Fin 3 → Fin 1104 :=
  ![inverseRegion0, inverseRegion1, inverseRegion2, inverseRegion3, inverseRegion4, inverseRegion5]

private def inverseCode (code : Code) : Fin 1104 :=
  inverseTable code.1 code.2.1 code.2.2

private theorem forward_admissible_block0 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 0 offset)) := by
  decide +kernel

private theorem forward_admissible_block1 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 1 offset)) := by
  decide +kernel

private theorem forward_admissible_block2 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 2 offset)) := by
  decide +kernel

private theorem forward_admissible_block3 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 3 offset)) := by
  decide +kernel

private theorem forward_admissible_block4 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 4 offset)) := by
  decide +kernel

private theorem forward_admissible_block5 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 5 offset)) := by
  decide +kernel

private theorem forward_admissible_block6 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 6 offset)) := by
  decide +kernel

private theorem forward_admissible_block7 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 7 offset)) := by
  decide +kernel

private theorem forward_admissible_block8 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 8 offset)) := by
  decide +kernel

private theorem forward_admissible_block9 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 9 offset)) := by
  decide +kernel

private theorem forward_admissible_block10 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 10 offset)) := by
  decide +kernel

private theorem forward_admissible_block11 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 11 offset)) := by
  decide +kernel

private theorem forward_admissible_block12 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 12 offset)) := by
  decide +kernel

private theorem forward_admissible_block13 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 13 offset)) := by
  decide +kernel

private theorem forward_admissible_block14 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 14 offset)) := by
  decide +kernel

private theorem forward_admissible_block15 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 15 offset)) := by
  decide +kernel

private theorem forward_admissible_block16 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 16 offset)) := by
  decide +kernel

private theorem forward_admissible_block17 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 17 offset)) := by
  decide +kernel

private theorem forward_admissible_block18 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 18 offset)) := by
  decide +kernel

private theorem forward_admissible_block19 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 19 offset)) := by
  decide +kernel

private theorem forward_admissible_block20 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 20 offset)) := by
  decide +kernel

private theorem forward_admissible_block21 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 21 offset)) := by
  decide +kernel

private theorem forward_admissible_block22 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 22 offset)) := by
  decide +kernel

private theorem forward_admissible_block23 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 23 offset)) := by
  decide +kernel

private theorem forward_admissible_block24 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 24 offset)) := by
  decide +kernel

private theorem forward_admissible_block25 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 25 offset)) := by
  decide +kernel

private theorem forward_admissible_block26 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 26 offset)) := by
  decide +kernel

private theorem forward_admissible_block27 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 27 offset)) := by
  decide +kernel

private theorem forward_admissible_block28 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 28 offset)) := by
  decide +kernel

private theorem forward_admissible_block29 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 29 offset)) := by
  decide +kernel

private theorem forward_admissible_block30 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 30 offset)) := by
  decide +kernel

private theorem forward_admissible_block31 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 31 offset)) := by
  decide +kernel

private theorem forward_admissible_block32 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 32 offset)) := by
  decide +kernel

private theorem forward_admissible_block33 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 33 offset)) := by
  decide +kernel

private theorem forward_admissible_block34 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 34 offset)) := by
  decide +kernel

private theorem forward_admissible_block35 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 35 offset)) := by
  decide +kernel

private theorem forward_admissible_block36 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 36 offset)) := by
  decide +kernel

private theorem forward_admissible_block37 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 37 offset)) := by
  decide +kernel

private theorem forward_admissible_block38 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 38 offset)) := by
  decide +kernel

private theorem forward_admissible_block39 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 39 offset)) := by
  decide +kernel

private theorem forward_admissible_block40 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 40 offset)) := by
  decide +kernel

private theorem forward_admissible_block41 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 41 offset)) := by
  decide +kernel

private theorem forward_admissible_block42 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 42 offset)) := by
  decide +kernel

private theorem forward_admissible_block43 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 43 offset)) := by
  decide +kernel

private theorem forward_admissible_block44 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 44 offset)) := by
  decide +kernel

private theorem forward_admissible_block45 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 45 offset)) := by
  decide +kernel

private theorem forward_admissible_block46 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 46 offset)) := by
  decide +kernel

private theorem forward_admissible_block47 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 47 offset)) := by
  decide +kernel

private theorem forward_admissible_block48 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 48 offset)) := by
  decide +kernel

private theorem forward_admissible_block49 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 49 offset)) := by
  decide +kernel

private theorem forward_admissible_block50 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 50 offset)) := by
  decide +kernel

private theorem forward_admissible_block51 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 51 offset)) := by
  decide +kernel

private theorem forward_admissible_block52 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 52 offset)) := by
  decide +kernel

private theorem forward_admissible_block53 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 53 offset)) := by
  decide +kernel

private theorem forward_admissible_block54 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 54 offset)) := by
  decide +kernel

private theorem forward_admissible_block55 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 55 offset)) := by
  decide +kernel

private theorem forward_admissible_block56 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 56 offset)) := by
  decide +kernel

private theorem forward_admissible_block57 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 57 offset)) := by
  decide +kernel

private theorem forward_admissible_block58 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 58 offset)) := by
  decide +kernel

private theorem forward_admissible_block59 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 59 offset)) := by
  decide +kernel

private theorem forward_admissible_block60 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 60 offset)) := by
  decide +kernel

private theorem forward_admissible_block61 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 61 offset)) := by
  decide +kernel

private theorem forward_admissible_block62 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 62 offset)) := by
  decide +kernel

private theorem forward_admissible_block63 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 63 offset)) := by
  decide +kernel

private theorem forward_admissible_block64 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 64 offset)) := by
  decide +kernel

private theorem forward_admissible_block65 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 65 offset)) := by
  decide +kernel

private theorem forward_admissible_block66 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 66 offset)) := by
  decide +kernel

private theorem forward_admissible_block67 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 67 offset)) := by
  decide +kernel

private theorem forward_admissible_block68 : ∀ offset : Fin 16,
    Admissible (forwardCode (joinRow 68 offset)) := by
  decide +kernel

private theorem forward_admissible (row : Fin 1104) :
    Admissible (forwardCode row) := by
  have hblock (block : Fin 69) (offset : Fin 16) :
      Admissible (forwardCode (joinRow block offset)) := by
    fin_cases block
    · exact forward_admissible_block0 offset
    · exact forward_admissible_block1 offset
    · exact forward_admissible_block2 offset
    · exact forward_admissible_block3 offset
    · exact forward_admissible_block4 offset
    · exact forward_admissible_block5 offset
    · exact forward_admissible_block6 offset
    · exact forward_admissible_block7 offset
    · exact forward_admissible_block8 offset
    · exact forward_admissible_block9 offset
    · exact forward_admissible_block10 offset
    · exact forward_admissible_block11 offset
    · exact forward_admissible_block12 offset
    · exact forward_admissible_block13 offset
    · exact forward_admissible_block14 offset
    · exact forward_admissible_block15 offset
    · exact forward_admissible_block16 offset
    · exact forward_admissible_block17 offset
    · exact forward_admissible_block18 offset
    · exact forward_admissible_block19 offset
    · exact forward_admissible_block20 offset
    · exact forward_admissible_block21 offset
    · exact forward_admissible_block22 offset
    · exact forward_admissible_block23 offset
    · exact forward_admissible_block24 offset
    · exact forward_admissible_block25 offset
    · exact forward_admissible_block26 offset
    · exact forward_admissible_block27 offset
    · exact forward_admissible_block28 offset
    · exact forward_admissible_block29 offset
    · exact forward_admissible_block30 offset
    · exact forward_admissible_block31 offset
    · exact forward_admissible_block32 offset
    · exact forward_admissible_block33 offset
    · exact forward_admissible_block34 offset
    · exact forward_admissible_block35 offset
    · exact forward_admissible_block36 offset
    · exact forward_admissible_block37 offset
    · exact forward_admissible_block38 offset
    · exact forward_admissible_block39 offset
    · exact forward_admissible_block40 offset
    · exact forward_admissible_block41 offset
    · exact forward_admissible_block42 offset
    · exact forward_admissible_block43 offset
    · exact forward_admissible_block44 offset
    · exact forward_admissible_block45 offset
    · exact forward_admissible_block46 offset
    · exact forward_admissible_block47 offset
    · exact forward_admissible_block48 offset
    · exact forward_admissible_block49 offset
    · exact forward_admissible_block50 offset
    · exact forward_admissible_block51 offset
    · exact forward_admissible_block52 offset
    · exact forward_admissible_block53 offset
    · exact forward_admissible_block54 offset
    · exact forward_admissible_block55 offset
    · exact forward_admissible_block56 offset
    · exact forward_admissible_block57 offset
    · exact forward_admissible_block58 offset
    · exact forward_admissible_block59 offset
    · exact forward_admissible_block60 offset
    · exact forward_admissible_block61 offset
    · exact forward_admissible_block62 offset
    · exact forward_admissible_block63 offset
    · exact forward_admissible_block64 offset
    · exact forward_admissible_block65 offset
    · exact forward_admissible_block66 offset
    · exact forward_admissible_block67 offset
    · exact forward_admissible_block68 offset
  simpa only [join_split] using hblock (rowBlock row) (rowOffset row)

private theorem left_inverse_block0 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 0 offset)) = (joinRow 0 offset) := by
  decide +kernel

private theorem left_inverse_block1 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 1 offset)) = (joinRow 1 offset) := by
  decide +kernel

private theorem left_inverse_block2 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 2 offset)) = (joinRow 2 offset) := by
  decide +kernel

private theorem left_inverse_block3 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 3 offset)) = (joinRow 3 offset) := by
  decide +kernel

private theorem left_inverse_block4 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 4 offset)) = (joinRow 4 offset) := by
  decide +kernel

private theorem left_inverse_block5 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 5 offset)) = (joinRow 5 offset) := by
  decide +kernel

private theorem left_inverse_block6 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 6 offset)) = (joinRow 6 offset) := by
  decide +kernel

private theorem left_inverse_block7 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 7 offset)) = (joinRow 7 offset) := by
  decide +kernel

private theorem left_inverse_block8 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 8 offset)) = (joinRow 8 offset) := by
  decide +kernel

private theorem left_inverse_block9 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 9 offset)) = (joinRow 9 offset) := by
  decide +kernel

private theorem left_inverse_block10 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 10 offset)) = (joinRow 10 offset) := by
  decide +kernel

private theorem left_inverse_block11 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 11 offset)) = (joinRow 11 offset) := by
  decide +kernel

private theorem left_inverse_block12 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 12 offset)) = (joinRow 12 offset) := by
  decide +kernel

private theorem left_inverse_block13 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 13 offset)) = (joinRow 13 offset) := by
  decide +kernel

private theorem left_inverse_block14 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 14 offset)) = (joinRow 14 offset) := by
  decide +kernel

private theorem left_inverse_block15 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 15 offset)) = (joinRow 15 offset) := by
  decide +kernel

private theorem left_inverse_block16 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 16 offset)) = (joinRow 16 offset) := by
  decide +kernel

private theorem left_inverse_block17 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 17 offset)) = (joinRow 17 offset) := by
  decide +kernel

private theorem left_inverse_block18 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 18 offset)) = (joinRow 18 offset) := by
  decide +kernel

private theorem left_inverse_block19 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 19 offset)) = (joinRow 19 offset) := by
  decide +kernel

private theorem left_inverse_block20 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 20 offset)) = (joinRow 20 offset) := by
  decide +kernel

private theorem left_inverse_block21 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 21 offset)) = (joinRow 21 offset) := by
  decide +kernel

private theorem left_inverse_block22 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 22 offset)) = (joinRow 22 offset) := by
  decide +kernel

private theorem left_inverse_block23 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 23 offset)) = (joinRow 23 offset) := by
  decide +kernel

private theorem left_inverse_block24 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 24 offset)) = (joinRow 24 offset) := by
  decide +kernel

private theorem left_inverse_block25 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 25 offset)) = (joinRow 25 offset) := by
  decide +kernel

private theorem left_inverse_block26 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 26 offset)) = (joinRow 26 offset) := by
  decide +kernel

private theorem left_inverse_block27 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 27 offset)) = (joinRow 27 offset) := by
  decide +kernel

private theorem left_inverse_block28 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 28 offset)) = (joinRow 28 offset) := by
  decide +kernel

private theorem left_inverse_block29 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 29 offset)) = (joinRow 29 offset) := by
  decide +kernel

private theorem left_inverse_block30 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 30 offset)) = (joinRow 30 offset) := by
  decide +kernel

private theorem left_inverse_block31 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 31 offset)) = (joinRow 31 offset) := by
  decide +kernel

private theorem left_inverse_block32 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 32 offset)) = (joinRow 32 offset) := by
  decide +kernel

private theorem left_inverse_block33 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 33 offset)) = (joinRow 33 offset) := by
  decide +kernel

private theorem left_inverse_block34 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 34 offset)) = (joinRow 34 offset) := by
  decide +kernel

private theorem left_inverse_block35 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 35 offset)) = (joinRow 35 offset) := by
  decide +kernel

private theorem left_inverse_block36 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 36 offset)) = (joinRow 36 offset) := by
  decide +kernel

private theorem left_inverse_block37 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 37 offset)) = (joinRow 37 offset) := by
  decide +kernel

private theorem left_inverse_block38 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 38 offset)) = (joinRow 38 offset) := by
  decide +kernel

private theorem left_inverse_block39 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 39 offset)) = (joinRow 39 offset) := by
  decide +kernel

private theorem left_inverse_block40 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 40 offset)) = (joinRow 40 offset) := by
  decide +kernel

private theorem left_inverse_block41 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 41 offset)) = (joinRow 41 offset) := by
  decide +kernel

private theorem left_inverse_block42 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 42 offset)) = (joinRow 42 offset) := by
  decide +kernel

private theorem left_inverse_block43 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 43 offset)) = (joinRow 43 offset) := by
  decide +kernel

private theorem left_inverse_block44 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 44 offset)) = (joinRow 44 offset) := by
  decide +kernel

private theorem left_inverse_block45 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 45 offset)) = (joinRow 45 offset) := by
  decide +kernel

private theorem left_inverse_block46 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 46 offset)) = (joinRow 46 offset) := by
  decide +kernel

private theorem left_inverse_block47 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 47 offset)) = (joinRow 47 offset) := by
  decide +kernel

private theorem left_inverse_block48 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 48 offset)) = (joinRow 48 offset) := by
  decide +kernel

private theorem left_inverse_block49 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 49 offset)) = (joinRow 49 offset) := by
  decide +kernel

private theorem left_inverse_block50 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 50 offset)) = (joinRow 50 offset) := by
  decide +kernel

private theorem left_inverse_block51 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 51 offset)) = (joinRow 51 offset) := by
  decide +kernel

private theorem left_inverse_block52 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 52 offset)) = (joinRow 52 offset) := by
  decide +kernel

private theorem left_inverse_block53 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 53 offset)) = (joinRow 53 offset) := by
  decide +kernel

private theorem left_inverse_block54 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 54 offset)) = (joinRow 54 offset) := by
  decide +kernel

private theorem left_inverse_block55 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 55 offset)) = (joinRow 55 offset) := by
  decide +kernel

private theorem left_inverse_block56 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 56 offset)) = (joinRow 56 offset) := by
  decide +kernel

private theorem left_inverse_block57 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 57 offset)) = (joinRow 57 offset) := by
  decide +kernel

private theorem left_inverse_block58 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 58 offset)) = (joinRow 58 offset) := by
  decide +kernel

private theorem left_inverse_block59 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 59 offset)) = (joinRow 59 offset) := by
  decide +kernel

private theorem left_inverse_block60 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 60 offset)) = (joinRow 60 offset) := by
  decide +kernel

private theorem left_inverse_block61 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 61 offset)) = (joinRow 61 offset) := by
  decide +kernel

private theorem left_inverse_block62 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 62 offset)) = (joinRow 62 offset) := by
  decide +kernel

private theorem left_inverse_block63 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 63 offset)) = (joinRow 63 offset) := by
  decide +kernel

private theorem left_inverse_block64 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 64 offset)) = (joinRow 64 offset) := by
  decide +kernel

private theorem left_inverse_block65 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 65 offset)) = (joinRow 65 offset) := by
  decide +kernel

private theorem left_inverse_block66 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 66 offset)) = (joinRow 66 offset) := by
  decide +kernel

private theorem left_inverse_block67 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 67 offset)) = (joinRow 67 offset) := by
  decide +kernel

private theorem left_inverse_block68 : ∀ offset : Fin 16,
    inverseCode (forwardCode (joinRow 68 offset)) = (joinRow 68 offset) := by
  decide +kernel

private theorem left_inverse (row : Fin 1104) :
    inverseCode (forwardCode row) = row := by
  have hblock (block : Fin 69) (offset : Fin 16) :
      inverseCode (forwardCode (joinRow block offset)) = (joinRow block offset) := by
    fin_cases block
    · exact left_inverse_block0 offset
    · exact left_inverse_block1 offset
    · exact left_inverse_block2 offset
    · exact left_inverse_block3 offset
    · exact left_inverse_block4 offset
    · exact left_inverse_block5 offset
    · exact left_inverse_block6 offset
    · exact left_inverse_block7 offset
    · exact left_inverse_block8 offset
    · exact left_inverse_block9 offset
    · exact left_inverse_block10 offset
    · exact left_inverse_block11 offset
    · exact left_inverse_block12 offset
    · exact left_inverse_block13 offset
    · exact left_inverse_block14 offset
    · exact left_inverse_block15 offset
    · exact left_inverse_block16 offset
    · exact left_inverse_block17 offset
    · exact left_inverse_block18 offset
    · exact left_inverse_block19 offset
    · exact left_inverse_block20 offset
    · exact left_inverse_block21 offset
    · exact left_inverse_block22 offset
    · exact left_inverse_block23 offset
    · exact left_inverse_block24 offset
    · exact left_inverse_block25 offset
    · exact left_inverse_block26 offset
    · exact left_inverse_block27 offset
    · exact left_inverse_block28 offset
    · exact left_inverse_block29 offset
    · exact left_inverse_block30 offset
    · exact left_inverse_block31 offset
    · exact left_inverse_block32 offset
    · exact left_inverse_block33 offset
    · exact left_inverse_block34 offset
    · exact left_inverse_block35 offset
    · exact left_inverse_block36 offset
    · exact left_inverse_block37 offset
    · exact left_inverse_block38 offset
    · exact left_inverse_block39 offset
    · exact left_inverse_block40 offset
    · exact left_inverse_block41 offset
    · exact left_inverse_block42 offset
    · exact left_inverse_block43 offset
    · exact left_inverse_block44 offset
    · exact left_inverse_block45 offset
    · exact left_inverse_block46 offset
    · exact left_inverse_block47 offset
    · exact left_inverse_block48 offset
    · exact left_inverse_block49 offset
    · exact left_inverse_block50 offset
    · exact left_inverse_block51 offset
    · exact left_inverse_block52 offset
    · exact left_inverse_block53 offset
    · exact left_inverse_block54 offset
    · exact left_inverse_block55 offset
    · exact left_inverse_block56 offset
    · exact left_inverse_block57 offset
    · exact left_inverse_block58 offset
    · exact left_inverse_block59 offset
    · exact left_inverse_block60 offset
    · exact left_inverse_block61 offset
    · exact left_inverse_block62 offset
    · exact left_inverse_block63 offset
    · exact left_inverse_block64 offset
    · exact left_inverse_block65 offset
    · exact left_inverse_block66 offset
    · exact left_inverse_block67 offset
    · exact left_inverse_block68 offset
  simpa only [join_split] using hblock (rowBlock row) (rowOffset row)

private theorem right_inverse_region0 :
    ∀ (row : Fin 88) (double : Fin 3),
      Admissible (0, row, double) →
        forwardCode (inverseCode (0, row, double)) = (0, row, double) := by
  decide +kernel

private theorem right_inverse_region1 :
    ∀ (row : Fin 88) (double : Fin 3),
      Admissible (1, row, double) →
        forwardCode (inverseCode (1, row, double)) = (1, row, double) := by
  decide +kernel

private theorem right_inverse_region2 :
    ∀ (row : Fin 88) (double : Fin 3),
      Admissible (2, row, double) →
        forwardCode (inverseCode (2, row, double)) = (2, row, double) := by
  decide +kernel

private theorem right_inverse_region3 :
    ∀ (row : Fin 88) (double : Fin 3),
      Admissible (3, row, double) →
        forwardCode (inverseCode (3, row, double)) = (3, row, double) := by
  decide +kernel

private theorem right_inverse_region4 :
    ∀ (row : Fin 88) (double : Fin 3),
      Admissible (4, row, double) →
        forwardCode (inverseCode (4, row, double)) = (4, row, double) := by
  decide +kernel

private theorem right_inverse_region5 :
    ∀ (row : Fin 88) (double : Fin 3),
      Admissible (5, row, double) →
        forwardCode (inverseCode (5, row, double)) = (5, row, double) := by
  decide +kernel

private theorem right_inverse (code : Code) (h : Admissible code) :
    forwardCode (inverseCode code) = code := by
  rcases code with ⟨region, row, double⟩
  fin_cases region
  · exact right_inverse_region0 row double h
  · exact right_inverse_region1 row double h
  · exact right_inverse_region2 row double h
  · exact right_inverse_region3 row double h
  · exact right_inverse_region4 row double h
  · exact right_inverse_region5 row double h

private def forwardCell (row : Fin 1104) : ChildCell :=
  cellOfCode (forwardCode row) (forward_admissible row)

private def RowData (row : Fin 1104) : Prop :=
  0 < RecStage.n2 row ∧
  (∀ i : Fin 3, RecStage.parent2 row i =
    ((forwardCell row).2.2.val
      ((ReleasedJointInterior.roleEquiv (forwardCell row).1).symm i)).val) ∧
  RecStage.n2 row = childMass (forwardCell row) ∧
  (RecStage.l2At row).2.2 =
    (RecStage.cellRec (forwardCell row).1 (forwardCell row).2.1
      (forwardCell row).2.2).2

private instance (row : Fin 1104) : Decidable (RowData row) := by
  unfold RowData
  infer_instance

private theorem row_data_block0 : ∀ offset : Fin 16,
    RowData (joinRow 0 offset) := by
  decide +kernel

private theorem row_data_block1 : ∀ offset : Fin 16,
    RowData (joinRow 1 offset) := by
  decide +kernel

private theorem row_data_block2 : ∀ offset : Fin 16,
    RowData (joinRow 2 offset) := by
  decide +kernel

private theorem row_data_block3 : ∀ offset : Fin 16,
    RowData (joinRow 3 offset) := by
  decide +kernel

private theorem row_data_block4 : ∀ offset : Fin 16,
    RowData (joinRow 4 offset) := by
  decide +kernel

private theorem row_data_block5 : ∀ offset : Fin 16,
    RowData (joinRow 5 offset) := by
  decide +kernel

private theorem row_data_block6 : ∀ offset : Fin 16,
    RowData (joinRow 6 offset) := by
  decide +kernel

private theorem row_data_block7 : ∀ offset : Fin 16,
    RowData (joinRow 7 offset) := by
  decide +kernel

private theorem row_data_block8 : ∀ offset : Fin 16,
    RowData (joinRow 8 offset) := by
  decide +kernel

private theorem row_data_block9 : ∀ offset : Fin 16,
    RowData (joinRow 9 offset) := by
  decide +kernel

private theorem row_data_block10 : ∀ offset : Fin 16,
    RowData (joinRow 10 offset) := by
  decide +kernel

private theorem row_data_block11 : ∀ offset : Fin 16,
    RowData (joinRow 11 offset) := by
  decide +kernel

private theorem row_data_block12 : ∀ offset : Fin 16,
    RowData (joinRow 12 offset) := by
  decide +kernel

private theorem row_data_block13 : ∀ offset : Fin 16,
    RowData (joinRow 13 offset) := by
  decide +kernel

private theorem row_data_block14 : ∀ offset : Fin 16,
    RowData (joinRow 14 offset) := by
  decide +kernel

private theorem row_data_block15 : ∀ offset : Fin 16,
    RowData (joinRow 15 offset) := by
  decide +kernel

private theorem row_data_block16 : ∀ offset : Fin 16,
    RowData (joinRow 16 offset) := by
  decide +kernel

private theorem row_data_block17 : ∀ offset : Fin 16,
    RowData (joinRow 17 offset) := by
  decide +kernel

private theorem row_data_block18 : ∀ offset : Fin 16,
    RowData (joinRow 18 offset) := by
  decide +kernel

private theorem row_data_block19 : ∀ offset : Fin 16,
    RowData (joinRow 19 offset) := by
  decide +kernel

private theorem row_data_block20 : ∀ offset : Fin 16,
    RowData (joinRow 20 offset) := by
  decide +kernel

private theorem row_data_block21 : ∀ offset : Fin 16,
    RowData (joinRow 21 offset) := by
  decide +kernel

private theorem row_data_block22 : ∀ offset : Fin 16,
    RowData (joinRow 22 offset) := by
  decide +kernel

private theorem row_data_block23 : ∀ offset : Fin 16,
    RowData (joinRow 23 offset) := by
  decide +kernel

private theorem row_data_block24 : ∀ offset : Fin 16,
    RowData (joinRow 24 offset) := by
  decide +kernel

private theorem row_data_block25 : ∀ offset : Fin 16,
    RowData (joinRow 25 offset) := by
  decide +kernel

private theorem row_data_block26 : ∀ offset : Fin 16,
    RowData (joinRow 26 offset) := by
  decide +kernel

private theorem row_data_block27 : ∀ offset : Fin 16,
    RowData (joinRow 27 offset) := by
  decide +kernel

private theorem row_data_block28 : ∀ offset : Fin 16,
    RowData (joinRow 28 offset) := by
  decide +kernel

private theorem row_data_block29 : ∀ offset : Fin 16,
    RowData (joinRow 29 offset) := by
  decide +kernel

private theorem row_data_block30 : ∀ offset : Fin 16,
    RowData (joinRow 30 offset) := by
  decide +kernel

private theorem row_data_block31 : ∀ offset : Fin 16,
    RowData (joinRow 31 offset) := by
  decide +kernel

private theorem row_data_block32 : ∀ offset : Fin 16,
    RowData (joinRow 32 offset) := by
  decide +kernel

private theorem row_data_block33 : ∀ offset : Fin 16,
    RowData (joinRow 33 offset) := by
  decide +kernel

private theorem row_data_block34 : ∀ offset : Fin 16,
    RowData (joinRow 34 offset) := by
  decide +kernel

private theorem row_data_block35 : ∀ offset : Fin 16,
    RowData (joinRow 35 offset) := by
  decide +kernel

private theorem row_data_block36 : ∀ offset : Fin 16,
    RowData (joinRow 36 offset) := by
  decide +kernel

private theorem row_data_block37 : ∀ offset : Fin 16,
    RowData (joinRow 37 offset) := by
  decide +kernel

private theorem row_data_block38 : ∀ offset : Fin 16,
    RowData (joinRow 38 offset) := by
  decide +kernel

private theorem row_data_block39 : ∀ offset : Fin 16,
    RowData (joinRow 39 offset) := by
  decide +kernel

private theorem row_data_block40 : ∀ offset : Fin 16,
    RowData (joinRow 40 offset) := by
  decide +kernel

private theorem row_data_block41 : ∀ offset : Fin 16,
    RowData (joinRow 41 offset) := by
  decide +kernel

private theorem row_data_block42 : ∀ offset : Fin 16,
    RowData (joinRow 42 offset) := by
  decide +kernel

private theorem row_data_block43 : ∀ offset : Fin 16,
    RowData (joinRow 43 offset) := by
  decide +kernel

private theorem row_data_block44 : ∀ offset : Fin 16,
    RowData (joinRow 44 offset) := by
  decide +kernel

private theorem row_data_block45 : ∀ offset : Fin 16,
    RowData (joinRow 45 offset) := by
  decide +kernel

private theorem row_data_block46 : ∀ offset : Fin 16,
    RowData (joinRow 46 offset) := by
  decide +kernel

private theorem row_data_block47 : ∀ offset : Fin 16,
    RowData (joinRow 47 offset) := by
  decide +kernel

private theorem row_data_block48 : ∀ offset : Fin 16,
    RowData (joinRow 48 offset) := by
  decide +kernel

private theorem row_data_block49 : ∀ offset : Fin 16,
    RowData (joinRow 49 offset) := by
  decide +kernel

private theorem row_data_block50 : ∀ offset : Fin 16,
    RowData (joinRow 50 offset) := by
  decide +kernel

private theorem row_data_block51 : ∀ offset : Fin 16,
    RowData (joinRow 51 offset) := by
  decide +kernel

private theorem row_data_block52 : ∀ offset : Fin 16,
    RowData (joinRow 52 offset) := by
  decide +kernel

private theorem row_data_block53 : ∀ offset : Fin 16,
    RowData (joinRow 53 offset) := by
  decide +kernel

private theorem row_data_block54 : ∀ offset : Fin 16,
    RowData (joinRow 54 offset) := by
  decide +kernel

private theorem row_data_block55 : ∀ offset : Fin 16,
    RowData (joinRow 55 offset) := by
  decide +kernel

private theorem row_data_block56 : ∀ offset : Fin 16,
    RowData (joinRow 56 offset) := by
  decide +kernel

private theorem row_data_block57 : ∀ offset : Fin 16,
    RowData (joinRow 57 offset) := by
  decide +kernel

private theorem row_data_block58 : ∀ offset : Fin 16,
    RowData (joinRow 58 offset) := by
  decide +kernel

private theorem row_data_block59 : ∀ offset : Fin 16,
    RowData (joinRow 59 offset) := by
  decide +kernel

private theorem row_data_block60 : ∀ offset : Fin 16,
    RowData (joinRow 60 offset) := by
  decide +kernel

private theorem row_data_block61 : ∀ offset : Fin 16,
    RowData (joinRow 61 offset) := by
  decide +kernel

private theorem row_data_block62 : ∀ offset : Fin 16,
    RowData (joinRow 62 offset) := by
  decide +kernel

private theorem row_data_block63 : ∀ offset : Fin 16,
    RowData (joinRow 63 offset) := by
  decide +kernel

private theorem row_data_block64 : ∀ offset : Fin 16,
    RowData (joinRow 64 offset) := by
  decide +kernel

private theorem row_data_block65 : ∀ offset : Fin 16,
    RowData (joinRow 65 offset) := by
  decide +kernel

private theorem row_data_block66 : ∀ offset : Fin 16,
    RowData (joinRow 66 offset) := by
  decide +kernel

private theorem row_data_block67 : ∀ offset : Fin 16,
    RowData (joinRow 67 offset) := by
  decide +kernel

private theorem row_data_block68 : ∀ offset : Fin 16,
    RowData (joinRow 68 offset) := by
  decide +kernel

private theorem row_data (row : Fin 1104) :
    RowData row := by
  have hblock (block : Fin 69) (offset : Fin 16) :
      RowData (joinRow block offset) := by
    fin_cases block
    · exact row_data_block0 offset
    · exact row_data_block1 offset
    · exact row_data_block2 offset
    · exact row_data_block3 offset
    · exact row_data_block4 offset
    · exact row_data_block5 offset
    · exact row_data_block6 offset
    · exact row_data_block7 offset
    · exact row_data_block8 offset
    · exact row_data_block9 offset
    · exact row_data_block10 offset
    · exact row_data_block11 offset
    · exact row_data_block12 offset
    · exact row_data_block13 offset
    · exact row_data_block14 offset
    · exact row_data_block15 offset
    · exact row_data_block16 offset
    · exact row_data_block17 offset
    · exact row_data_block18 offset
    · exact row_data_block19 offset
    · exact row_data_block20 offset
    · exact row_data_block21 offset
    · exact row_data_block22 offset
    · exact row_data_block23 offset
    · exact row_data_block24 offset
    · exact row_data_block25 offset
    · exact row_data_block26 offset
    · exact row_data_block27 offset
    · exact row_data_block28 offset
    · exact row_data_block29 offset
    · exact row_data_block30 offset
    · exact row_data_block31 offset
    · exact row_data_block32 offset
    · exact row_data_block33 offset
    · exact row_data_block34 offset
    · exact row_data_block35 offset
    · exact row_data_block36 offset
    · exact row_data_block37 offset
    · exact row_data_block38 offset
    · exact row_data_block39 offset
    · exact row_data_block40 offset
    · exact row_data_block41 offset
    · exact row_data_block42 offset
    · exact row_data_block43 offset
    · exact row_data_block44 offset
    · exact row_data_block45 offset
    · exact row_data_block46 offset
    · exact row_data_block47 offset
    · exact row_data_block48 offset
    · exact row_data_block49 offset
    · exact row_data_block50 offset
    · exact row_data_block51 offset
    · exact row_data_block52 offset
    · exact row_data_block53 offset
    · exact row_data_block54 offset
    · exact row_data_block55 offset
    · exact row_data_block56 offset
    · exact row_data_block57 offset
    · exact row_data_block58 offset
    · exact row_data_block59 offset
    · exact row_data_block60 offset
    · exact row_data_block61 offset
    · exact row_data_block62 offset
    · exact row_data_block63 offset
    · exact row_data_block64 offset
    · exact row_data_block65 offset
    · exact row_data_block66 offset
    · exact row_data_block67 offset
    · exact row_data_block68 offset
  simpa only [join_split] using hblock (rowBlock row) (rowOffset row)


private def positiveChild (row : Fin 1104) : PositiveChild :=
  ⟨forwardCell row, shape_positive (forwardCode row).2.2,
    (row_data row).2.2.1 ▸ (row_data row).1⟩

private def reindex : Fin 1104 ≃ PositiveChild where
  toFun := positiveChild
  invFun cell := inverseCode (codeOfCell cell.val)
  left_inv row := by
    change inverseCode (codeOfCell
      (cellOfCode (forwardCode row) (forward_admissible row))) = row
    rw [codeOf_cellOf]
    exact left_inverse row
  right_inv cell := by
    apply Subtype.ext
    change cellOfCode (forwardCode (inverseCode (codeOfCell cell.val)))
      (forward_admissible (inverseCode (codeOfCell cell.val))) = cell.val
    exact (cellOf_congr
      (right_inverse (codeOfCell cell.val) (codeOf_admissible cell.val cell.property.1))
      (forward_admissible (inverseCode (codeOfCell cell.val)))
      (codeOf_admissible cell.val cell.property.1)).trans
        (cellOf_codeOf cell.val cell.property.1)

private def closedWeight (grade parameter : ℕ) (u v : Fin 3) : ℕ :=
  if v.val = grade - u.val then
    if grade = 2 then (![parameter, RecStage.D - 2 * parameter, parameter] : Fin 3 → ℕ) u
    else (![RecStage.D / 2, RecStage.D / 2, 0] : Fin 3 → ℕ) u
  else 0

private theorem childW_closed (double : Fin 3) (parameter : ℕ)
    (hparameter : 2 * parameter ≤ RecStage.D) (i u v : Fin 3) :
    RecStage.childW (shape double 0).val (shape double 1).val (shape double 2).val
      parameter i.val u.val v.val = closedWeight (shape double i).val parameter u v := by
  simp only [RecStage.D] at hparameter
  fin_cases double <;> fin_cases i <;> fin_cases u <;> fin_cases v <;>
    simp [shape, closedWeight, RecStage.childW, RecStage.elemT, RecStage.coord,
      RecStage.jw, RecStage.D] <;> omega

private theorem cellDist_entry (region : Fin 6) (i : Fin 3) (row : Fin 88)
    (cell : RecursiveThinSplit.Split 4 (RecStage.parent3 region row)) (u v : Fin 3) :
    (RecStage.cellDist region i row cell).getD (3 * u.val + v.val) 0 =
      RecStage.childW (cell.val 0).val (cell.val 1).val (cell.val 2).val
        (RecStage.cellRec region row cell).2 i.val u.val v.val := by
  fin_cases u <;> fin_cases v <;> rfl

private theorem forward_dist (row : Fin 1104) (i u v : Fin 3) :
    (RecStage.cellDist (forwardCell row).1
      ((ReleasedJointInterior.roleEquiv (forwardCell row).1).symm i)
      (forwardCell row).2.1 (forwardCell row).2.2).getD (3 * u.val + v.val) 0 =
      if v.val = RecStage.parent2 row i - u.val then L2Cert.Jm row i u else 0 := by
  rw [cellDist_entry, ← (row_data row).2.2.2]
  change RecStage.childW (shape (forwardCode row).2.2 0).val
    (shape (forwardCode row).2.2 1).val (shape (forwardCode row).2.2 2).val
    (RecStage.l2At row).2.2
    ((ReleasedJointInterior.roleEquiv (forwardCell row).1).symm i).val u.val v.val = _
  rw [childW_closed _ _ (mme_released_recursive_level2_shapes.2 row)]
  change closedWeight
    ((forwardCell row).2.2.val ((ReleasedJointInterior.roleEquiv (forwardCell row).1).symm i)).val
    (RecStage.l2At row).2.2 u v = _
  rw [← (row_data row).2.1 i]
  unfold closedWeight
  rw [mme_released_recursive_level2_marginals.2.2.2 row i u]

private theorem forward_marginal (row : Fin 1104) (i : Fin 3) (word : CompleteWord 2) :
    RecStage.D * RecStage.mu3 (forwardCell row).1
      ((ReleasedJointInterior.roleEquiv (forwardCell row).1).symm i)
      (forwardCell row).2 word =
    RecStage.n2 row *
      (if (word 1).val = RecStage.parent2 row i - (word 0).val then
        L2Cert.Jm row i (word 0) else 0) := by
  change RecStage.D * (childMass (forwardCell row) *
    (RecStage.cellDist (forwardCell row).1
      ((ReleasedJointInterior.roleEquiv (forwardCell row).1).symm i)
      (forwardCell row).2.1 (forwardCell row).2.2).getD
        (3 * (word 0).val + (word 1).val) 0 / RecStage.D) = _
  rw [← (row_data row).2.2.1, forward_dist]
  apply Nat.mul_div_cancel'
  refine ⟨(RecStage.l2At row).2.1 * RecStage.D *
    (if (word 1).val = RecStage.parent2 row i - (word 0).val then
      L2Cert.Jm row i (word 0) else 0), ?_⟩
  simp only [RecStage.n2, pow_two]
  ring

end RecursiveContinuationReindex

open RecursiveContinuationReindex

/-- Every positive regional child is one pooled level-two row. The equivalence
preserves its physical grades, mass, split parameter and all word marginals. -/
theorem solution :
    ∃ reindex : Fin 1104 ≃
      {cell : (region : Fin 6) × Cell 4 88 (RecStage.parent3 region) //
        (∀ i : Fin 3, 0 < (cell.2.2.val i).val) ∧
        0 < RecStage.m3 cell.1 cell.2.1 cell.2.2 +
          RecStage.m3 cell.1 cell.2.1
            (complement (RecStage.htotal3 cell.1 cell.2.1) cell.2.2)},
      ∀ row : Fin 1104,
        (∀ i : Fin 3, RecStage.parent2 row i =
          ((reindex row).val.2.2.val
            ((ReleasedJointInterior.roleEquiv (reindex row).val.1).symm i)).val) ∧
        RecStage.n2 row =
          RecStage.m3 (reindex row).val.1 (reindex row).val.2.1 (reindex row).val.2.2 +
          RecStage.m3 (reindex row).val.1 (reindex row).val.2.1
            (complement (RecStage.htotal3 (reindex row).val.1 (reindex row).val.2.1)
              (reindex row).val.2.2) ∧
        (RecStage.l2At row).2.2 =
          (RecStage.cellRec (reindex row).val.1 (reindex row).val.2.1
            (reindex row).val.2.2).2 ∧
        (∀ (i : Fin 3) (word : CompleteWord 2),
          RecStage.D * RecStage.mu3 (reindex row).val.1
            ((ReleasedJointInterior.roleEquiv (reindex row).val.1).symm i)
            (reindex row).val.2 word =
          RecStage.n2 row *
            (if (word 1).val = RecStage.parent2 row i - (word 0).val then
              L2Cert.Jm row i (word 0) else 0)) := by
  refine ⟨reindex, fun row ↦ ?_⟩
  exact ⟨(row_data row).2.1, (row_data row).2.2.1,
    (row_data row).2.2.2, forward_marginal row⟩

#print axioms solution
