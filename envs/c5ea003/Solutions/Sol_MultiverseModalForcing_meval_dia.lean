-- Prove2me | solution 1 for MultiverseModalForcing.meval_dia
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:30:21.306574+00:00
-- url     : https://prove2.me/submissions/8ab32774-64f6-486c-a91b-7bc1edd0d170

import Mathlib
import Definitions.Def_Applications_ProofTheoryAndLogic_MultiverseModalForcing
open MultiverseModalForcing in
theorem solution {α} (R : World α → World α → Prop) (M : Multiverse α)
    (w : World α) (p : MSentence α) :
    meval R M w (MSentence.dia p) ↔ ∃ v, R w v ∧ v ∈ M ∧ meval R M v p := by
  -- `◇p = ¬□¬p`
  simp only [MSentence.dia, meval, not_forall, not_not, exists_prop]
