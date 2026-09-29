-- Prove2me | Theorems.Thm_mme_dwz_table2_completed_useful_family_supported_compatible
-- name    : mme_dwz_table2_completed_useful_family_supported_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:45:45.794787+00:00
-- url     : https://prove2.me/theorems/a740daff-1824-4031-acb7-525d2f8aabac
-- title:
--   Supported mixed addresses from completed useful blocks satisfy literal Step-2 compatibility
-- statement:
--   Let a retained family of Table-2 outer words share one coarse $Z$ word and be isolated by their coarse $Y$ words.  Equip each retained copy with a literal useful fine-$Z$ block and complete it by the canonical fine $X/Y$ selector.  For any mixed choice of one retained copy in each tensor mode, if the resulting fine block is nonzero at every position, then the selected $Z$ address satisfies the literal DWZ Step-2 compatibility equations with the X/Y owner.
--
--   Thus the concrete useful-block construction supplies the `hSupportedCompatible` premise of the nonhole direct-sum theorem.  Nonvanishing remains an explicit premise, and no hole mask is asserted.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Steps 1 and 2, printed pp. 51--54 (PDF pp. 52--55), specialized to Table 2; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_completed_useful_family_step1_premises
import Theorems.Thm_mme_dwz_table2_retained_fine_address_supported_compatible

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v w

set_option autoImplicit false

theorem mme_dwz_table2_completed_useful_family_supported_compatible
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
  sorry
