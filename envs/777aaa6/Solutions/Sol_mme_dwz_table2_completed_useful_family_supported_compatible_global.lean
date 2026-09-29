-- Prove2me | solution 1 for mme_dwz_table2_completed_useful_family_supported_compatible_global
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T21:08:27.551096+00:00
-- url     : https://prove2.me/submissions/e011c622-75c6-4f29-a619-84f3eab39e90

import Theorems.Thm_mme_dwz_table2_completed_useful_family_supported_compatible

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v w

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (q m : ℕ)
    {Copy : Type v} {Position : Type w} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    (small : ∀ j : Copy,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (hYIsolated : ∀ j j',
      (fun r ↦ MME.DWZSquare.shapeY (outer j r)) =
        (fun r ↦ MME.DWZSquare.shapeY (outer j' r)) → j = j')
    (hSupportedOwners : ∀ js : Fin 3 → Copy,
      (let left : Copy → Fin 3 → Position → Fin 3 := fun j ↦
          completedFineLeft (outer j) (small j).1 (small j).2.1
       let right : Copy → Fin 3 → Position → Fin 3 := fun j ↦
          completedFineRight (outer j) (small j).1 (small j).2.1
       ∀ r : Position,
        (cwSquareFineSplitGrading K q).blockTensor
          (fun i ↦ retainedFineAddress left right (js i) i r) ≠ 0) →
      js 0 = js 1 ∧
        ∀ r, MME.DWZSquare.shapeZ (outer (js 0) r) =
          MME.DWZSquare.shapeZ (outer (js 2) r)) :
    let left : Copy → Fin 3 → Position → Fin 3 := fun j ↦
      completedFineLeft (outer j) (small j).1 (small j).2.1
    let right : Copy → Fin 3 → Position → Fin 3 := fun j ↦
      completedFineRight (outer j) (small j).1 (small j).2.1
    ∀ js : Fin 3 → Copy,
      (∀ r : Position,
        (cwSquareFineSplitGrading K q).blockTensor
          (fun i ↦ retainedFineAddress left right (js i) i r) ≠ 0) →
      retainedFineCompatible m outer
        (retainedFineAddress left right (js 2) 2) (js 0) := by
  classical
  dsimp only
  intro js hsupported
  have howners := hSupportedOwners js hsupported
  let SameZ := {j : Copy // ∀ r,
    MME.DWZSquare.shapeZ (outer j r) =
      MME.DWZSquare.shapeZ (outer (js 2) r)}
  let outer' : SameZ → Position → Fin 15 := fun j ↦ outer j.1
  let small' : ∀ j : SameZ,
      MME.DWZTable2StandardForm.UsefulBlock m (outer' j) :=
    fun j ↦ small j.1
  have hz0 : ∀ r, MME.DWZSquare.shapeZ (outer (js 0) r) =
      MME.DWZSquare.shapeZ (outer (js 2) r) := howners.2
  have hz1 : ∀ r, MME.DWZSquare.shapeZ (outer (js 1) r) =
      MME.DWZSquare.shapeZ (outer (js 2) r) := by
    rw [← howners.1]
    exact hz0
  have hz2 : ∀ r, MME.DWZSquare.shapeZ (outer (js 2) r) =
      MME.DWZSquare.shapeZ (outer (js 2) r) := fun _ ↦ rfl
  let js' : Fin 3 → SameZ := fun i ↦ ⟨js i, by
    fin_cases i
    · exact hz0
    · exact hz1
    · exact hz2⟩
  have hCommonZ : ∀ a b : SameZ, ∀ r,
      MME.DWZSquare.shapeZ (outer' a r) =
        MME.DWZSquare.shapeZ (outer' b r) := by
    intro a b r
    exact (a.2 r).trans (b.2 r).symm
  have hYIsolated' : ∀ a b : SameZ,
      (fun r ↦ MME.DWZSquare.shapeY (outer' a r)) =
        (fun r ↦ MME.DWZSquare.shapeY (outer' b r)) → a = b := by
    intro a b hab
    apply Subtype.ext
    exact hYIsolated a.1 b.1 hab
  have hsupported' :
      let left : SameZ → Fin 3 → Position → Fin 3 := fun j ↦
        completedFineLeft (outer' j) (small' j).1 (small' j).2.1
      let right : SameZ → Fin 3 → Position → Fin 3 := fun j ↦
        completedFineRight (outer' j) (small' j).1 (small' j).2.1
      ∀ r : Position,
        (cwSquareFineSplitGrading K q).blockTensor
          (fun i ↦ retainedFineAddress left right (js' i) i r) ≠ 0 := by
    dsimp only [outer', small', js']
    simpa only using hsupported
  have hlocal :=
    mme_dwz_table2_completed_useful_family_supported_compatible
      K q m outer' small' hCommonZ hYIsolated' js' hsupported'
  simpa only [outer', small', js'] using hlocal
