-- Prove2me | solution 1 for mme_dwz_useful_block_nonhole_to_completed_fine_address_nonhole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:17:03.479438+00:00
-- url     : https://prove2.me/submissions/c68e3f52-e82d-47fe-a394-e1c5d41d04a1

import Theorems.Thm_mme_dwz_completed_fine_z_address_eq_useful_block_encode
import Definitions.Def_mme_dwz_retained_fine_compatibility
import Definitions.Def_mme_dwz_step2_broken_copy

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {Copy : Type v} {Position : Type u}
    [Fintype Copy] [DecidableEq Copy]
    [Fintype Position] [DecidableEq Position]
    (outer : Copy → Position → Fin 15)
    [DecidableRel (retainedFineCompatible m outer)]
    (small : ∀ j : Copy,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (j : Copy)
    (sourceCompatible :
      MME.DWZTable2StandardForm.UsefulBlock m (outer j) → Copy → Prop)
    [DecidableRel sourceCompatible]
    (hSourceNonhole :
      small j ∈ (MME.DWZStep2.brokenCopy sourceCompatible
        (fun _ _ ↦ True) j).nonholes)
    (hCompatibleIff : ∀ j' : Copy,
      sourceCompatible (small j) j' ↔
        retainedFineCompatible m outer
          (fun t ↦
            fineSplitGrade ((small j).1 t).1 ((small j).1 t).2) j') :
    let left : Copy → Fin 3 → Position → Fin 3 := fun j' ↦
      completedFineLeft (outer j') (small j').1 (small j').2.1
    let right : Copy → Fin 3 → Position → Fin 3 := fun j' ↦
      completedFineRight (outer j') (small j').1 (small j').2.1
    retainedFineAddress left right j 2 ∈
      (MME.DWZStep2.brokenCopy
        (retainedFineCompatible m outer) (fun _ _ ↦ True) j).nonholes := by
  classical
  dsimp only
  rw [mme_dwz_completed_fine_z_address_eq_useful_block_encode
    m outer small j]
  simp only [MME.DWZStep2.brokenCopy, Finset.mem_filter,
    Finset.mem_univ, true_and, MME.DWZStep2.Keeps]
  have hSource :
      sourceCompatible (small j) j ∧
        ∀ j', sourceCompatible (small j) j' → j' = j := by
    simpa only [MME.DWZStep2.brokenCopy, Finset.mem_filter,
      Finset.mem_univ, true_and, MME.DWZStep2.Keeps] using hSourceNonhole
  refine ⟨(hCompatibleIff j).mp hSource.1, ?_⟩
  intro j' hj'
  exact hSource.2 j' ((hCompatibleIff j').mpr hj')
