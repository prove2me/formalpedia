-- Prove2me | solution 1 for mme_dwz_table2_completed_useful_family_supported_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:46:27.703555+00:00
-- url     : https://prove2.me/submissions/3b61800a-3547-4409-8acb-0d6fe1ad976b

import Theorems.Thm_mme_dwz_table2_completed_useful_family_step1_premises
import Theorems.Thm_mme_dwz_table2_retained_fine_address_supported_compatible

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
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r))
    (hYIsolated : ∀ j j',
      (fun r ↦ DWZSquare.shapeY (outer j r)) =
        (fun r ↦ DWZSquare.shapeY (outer j' r)) → j = j') :
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
  dsimp only
  have h := mme_dwz_table2_completed_useful_family_step1_premises
    m outer small
  exact mme_dwz_table2_retained_fine_address_supported_compatible
    K q m outer
      (fun j ↦ completedFineLeft (outer j) (small j).1 (small j).2.1)
      (fun j ↦ completedFineRight (outer j) (small j).1 (small j).2.1)
      h.1 hCommonZ hYIsolated h.2.1 h.2.2.1 h.2.2.2
