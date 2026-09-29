-- Prove2me | Theorems.Thm_mme_dwz_component_word_pointwise_coarse
-- name    : mme_dwz_component_word_pointwise_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:08:14.235191+00:00
-- url     : https://prove2.me/theorems/0a89a3e9-4e21-44bd-b520-a4eb5ab92a90
-- title:
--   Every component-word letter has the prescribed coarse Z grade
-- statement:
--   Fix a Table-2 component $s$, whose coarse $Z$ grade is $k_s$, and a canonical $Z$-basis word in the prescribed component power. At every word position $r$, let $(a_r,b_r)$ be the left and right fine grades of its canonical coordinate pair. Then
--
--   $$
--   a_r+b_r=k_s,
--   $$
--
--   where the sum is interpreted by the DWZ fine-to-coarse map. Thus every word in the component basis already satisfies the pointwise coarse compatibility required in Definition 5.3; availability only has to impose the remaining histogram condition from Definition 5.4.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.3--5.4, PDF p. 48 / printed p. 47; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_component_word_projection

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_component_word_pointwise_coarse
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
  sorry
