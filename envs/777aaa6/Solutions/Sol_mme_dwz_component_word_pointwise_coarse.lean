-- Prove2me | solution 1 for mme_dwz_component_word_pointwise_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T08:08:33.677698+00:00
-- url     : https://prove2.me/submissions/52c1b331-1c66-4f97-93f8-f5965debc4de

import Definitions.Def_mme_dwz_component_word_projection

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (s : Fin 15) (m : ℕ)
    (w : MME.DWZComponentRestriction.PowIndex
      (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m))
    (r : Fin (MME.DWZTable2Counts.component s * m)) :
    MME.DWZTable2Counts.coarseOf
        ((MME.DWZComponentRestriction.PowIndex.get _ w r).leftGrade,
          (MME.DWZComponentRestriction.PowIndex.get _ w r).rightGrade) =
      MME.DWZSquare.shapeZ s := by
  apply Fin.ext
  exact congrArg Fin.val
    (MME.DWZComponentRestriction.PowIndex.get _ w r).down.2
