-- Prove2me | Theorems.Thm_mme_dwz_table2_completed_useful_family_supported_compatible_global
-- name    : mme_dwz_table2_completed_useful_family_supported_compatible_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:06:40.696878+00:00
-- url     : https://prove2.me/theorems/9d4fb0de-3721-4e9d-9c59-ef01bbc786df
-- title:
--   Completed fine compatibility localizes to the supported mixed triple's coarse-Z fiber
-- statement:
--   Consider a family of completed useful fine blocks. Assume Y profiles isolate owners. For every mixed triple supported by the fine-split tensor, assume its X and Y owners coincide and the coarse Z word of that owner equals the coarse Z word of its Z owner. Then the selected completed fine Z address is compatible with the common X/Y owner. The result localizes the common-Z argument to the fiber determined by the supported triple, rather than imposing a global common-Z hypothesis on the whole family.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 1 and Claim 6.2; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_completed_useful_family_supported_compatible

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v w

set_option autoImplicit false

theorem mme_dwz_table2_completed_useful_family_supported_compatible_global
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
  sorry
