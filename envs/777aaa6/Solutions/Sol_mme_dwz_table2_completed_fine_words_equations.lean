-- Prove2me | solution 1 for mme_dwz_table2_completed_fine_words_equations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:07:09.658182+00:00
-- url     : https://prove2.me/submissions/001ea8c3-533f-4a04-8d50-7874d4404c28

import Definitions.Def_mme_dwz_table2_completed_fine_words

open MME
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Position : Type u} (outer : Position → Fin 15)
    (z : Position → Fin 3 × Fin 3)
    (hZ : ∀ t, MME.DWZTable2Counts.coarseOf (z t) =
      MME.DWZSquare.shapeZ (outer t)) :
    (∀ i t,
      (completedFineLeft outer z hZ i t).val +
          (completedFineRight outer z hZ i t).val =
        (cwSquareBlockType
          (MME.DWZSquare.shapeX (outer t))
          (MME.DWZSquare.shapeY (outer t))
          (MME.DWZSquare.shapeZ (outer t)) i).val) ∧
    (∀ t,
      (completedFineLeft outer z hZ 0 t).val +
          (completedFineLeft outer z hZ 1 t).val +
          (completedFineLeft outer z hZ 2 t).val = 2) ∧
    (∀ t,
      (completedFineRight outer z hZ 0 t).val +
          (completedFineRight outer z hZ 1 t).val +
          (completedFineRight outer z hZ 2 t).val = 2) ∧
    (∀ t,
      completedFineLeft outer z hZ 2 t = (z t).1 ∧
      completedFineRight outer z hZ 2 t = (z t).2) := by
  constructor
  · intro i t
    fin_cases i
    · exact (fineXYCompletion (outer t) (z t).1 (z t).2 (hZ t)).x_coarse
    · exact (fineXYCompletion (outer t) (z t).1 (z t).2 (hZ t)).y_coarse
    · change (z t).1.val + (z t).2.val =
        (MME.DWZSquare.shapeZ (outer t)).val
      exact congrArg Fin.val (hZ t)
  constructor
  · intro t
    exact (fineXYCompletion (outer t) (z t).1 (z t).2 (hZ t)).left_support
  constructor
  · intro t
    exact (fineXYCompletion (outer t) (z t).1 (z t).2 (hZ t)).right_support
  · intro t
    exact ⟨rfl, rfl⟩
