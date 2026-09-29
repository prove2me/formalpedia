-- Prove2me | solution 1 for mme_released_global_joint_counts_valid
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:22:30.586699+00:00
-- url     : https://prove2.me/submissions/74dd8fca-a616-4d5b-9d54-ea534296a731

import Definitions.Def_mme_released_global_profile_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

theorem solution :
    (∀ owner : Fin 6, ∑ s : Fin 45, alpha owner s = denominator) ∧
    (∀ owner : Fin 6, ∀ s : Fin 45,
      ((jointRows owner s).map Prod.snd).sum = denominator^4 ∧
      ∀ a ∈ jointRows owner s, ∀ i : Fin 3,
        RecursiveYZ.CWCells.grade (atom a.1 i) = ((shape s).val i).val) ∧
    Fintype.card Shape = 45 ∧ Fintype.card Word = 81 ∧
    (∀ owner : Fin 6, Function.Bijective (roles owner)) ∧
    (∀ (owner : Fin 6) (s : Fin 45) (i : Fin 3),
      (shape (sourceIndex owner s)).val (roles owner i) = (shape s).val i) := by
  have hα : ∀ owner : Fin 6, ∑ s : Fin 45, alpha owner s = denominator := by
    decide +kernel
  have hg : ∀ owner : Fin 6, ∀ s : Fin 45,
      ((jointRows owner s).map Prod.snd).sum = denominator^4 ∧
      ∀ a ∈ jointRows owner s, ∀ i : Fin 3,
        RecursiveYZ.CWCells.grade (atom a.1 i) = ((shape s).val i).val := by
    decide +kernel
  refine ⟨hα,hg,?_,?_,?_,?_⟩
  · simpa using (Fintype.card_congr shapeEquiv).symm
  · norm_num [Word,CompleteSplit.CompleteWord]
  · decide +kernel
  · decide +kernel
