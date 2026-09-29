-- Prove2me | solution 1 for mme_complete_split_112_coupled_basis_label_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:18:42.371603+00:00
-- url     : https://prove2.me/submissions/01e87bdc-2d74-4754-be8b-f24d7f0aaa16

import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Mathlib.Tactic

set_option autoImplicit false

universe u

open MME MME.CompleteSplit112 Module
set_option warningAsError true

namespace MME.CompleteSplit112

private theorem coordBasis_eq_standard
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (c : DWZCanonical112Coord q s) :
    coordBasis K q s c = dwzCanonical112Vec K q s c := by
  fin_cases s <;> exact Pi.basisFun_apply K _ _

private theorem coordBasis_mem_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (c : DWZCanonical112Coord q s) :
    coordBasis K q s c ∈ (grading K q).classOf s (coordGrade q s c) := by
  exact Submodule.subset_span ⟨c, rfl, rfl⟩

private theorem canonical_outer_grade (q : ℕ) :
    cwSquareCoordGrade q 0 = 0 := by
  simp [cwSquareCoordGrade]

private theorem canonical_middle_grade (q : ℕ) (i : Fin q) :
    cwSquareCoordGrade q ⟨i.val + 1, by omega⟩ = 1 := by
  simp [cwSquareCoordGrade]
  omega

private theorem canonical_terminal_grade (q : ℕ) :
    cwSquareCoordGrade q ⟨q + 1, by omega⟩ = 2 := by
  simp [cwSquareCoordGrade]

/-- The full two-letter fine word of the literal canonical source pair is
the declared complete word of its actual coupled coordinate grade. -/
private theorem canonicalPair_fineWord
    (q : ℕ) (s : Fin 3) (c : DWZCanonical112Coord q s) :
    ![cwSquareCoordGrade q (dwzCanonical112Pair q s c).1,
      cwSquareCoordGrade q (dwzCanonical112Pair q s c).2] =
      fineWord s (coordGrade q s c) := by
  fin_cases s
  · rcases c with i | i <;>
      simp [dwzCanonical112Pair, coordGrade, fineWord,
        canonical_outer_grade, canonical_middle_grade]
  · rcases c with i | i <;>
      simp [dwzCanonical112Pair, coordGrade, fineWord,
        canonical_outer_grade, canonical_middle_grade]
  · rcases c with a | ij
    · fin_cases a <;>
        simp [dwzCanonical112Pair, coordGrade, fineWord,
          canonical_outer_grade, canonical_terminal_grade]
    · rcases ij with ⟨i, j⟩
      simp [dwzCanonical112Pair, coordGrade, fineWord, canonical_middle_grade]

private theorem liftedCoordBasis_eq_standard
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (c : LiftedCoord.{u} q s) :
    liftedCoordBasis K q s c = dwzCanonical112Vec K q s c.down := by
  exact ((coordBasis K q s).reindex_apply Equiv.ulift.symm c).trans
    (coordBasis_eq_standard K q s c.down)

private theorem liftedCoordBasis_mem_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (c : LiftedCoord.{u} q s) :
    liftedCoordBasis K q s c ∈ (grading K q).classOf s (liftedCoordGrade q s c) := by
  have heq : liftedCoordBasis K q s c = coordBasis K q s c.down :=
    (coordBasis K q s).reindex_apply Equiv.ulift.symm c
  rw [heq]
  exact coordBasis_mem_grade K q s c.down

end MME.CompleteSplit112


theorem solution
    (K : Type u) [Field K] (q : ℕ) :
    (∀ (s : Fin 3) (c : DWZCanonical112Coord q s),
      coordBasis K q s c = dwzCanonical112Vec K q s c) ∧
    (∀ (s : Fin 3) (c : DWZCanonical112Coord q s),
      ![cwSquareCoordGrade q (dwzCanonical112Pair q s c).1,
        cwSquareCoordGrade q (dwzCanonical112Pair q s c).2] =
        fineWord s (coordGrade q s c)) ∧
    (∀ (s : Fin 3) (c : LiftedCoord.{u} q s),
      liftedCoordBasis K q s c = dwzCanonical112Vec K q s c.down) ∧
    (∀ (s : Fin 3) (c : LiftedCoord.{u} q s),
      liftedCoordBasis K q s c ∈
        (grading K q).classOf s (liftedCoordGrade q s c)) := by
  exact ⟨coordBasis_eq_standard K q, canonicalPair_fineWord q,
    liftedCoordBasis_eq_standard K q, liftedCoordBasis_mem_grade K q⟩

