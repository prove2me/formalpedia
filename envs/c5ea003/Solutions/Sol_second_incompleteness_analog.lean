-- Prove2me | solution 1 for second_incompleteness_analog
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:11:19.239985+00:00
-- url     : https://prove2.me/submissions/0139d2a6-7286-474d-be6b-4eaa4fd43d21

import Mathlib
import Definitions.Def_Logic_StrangeLoops_Core
theorem solution (L : StrangeLoop)
    (cons_sentence : L.Sentence)
    (hcons : L.True_ cons_sentence ↔ ¬ L.Provable L.goedelSentence)
    (hformalized : L.Provable cons_sentence → L.Provable L.goedelSentence) :
    ¬ L.Provable cons_sentence := by
  intro hp
  -- proving consistency would prove the Gödel sentence, which soundness makes true,
  -- and a true Gödel sentence is unprovable
  have hG : L.Provable L.goedelSentence := hformalized hp
  have hT : L.True_ L.goedelSentence := L.sound _ hG
  exact (L.diag_spec (fun s => ¬ L.Provable s)).1 hT hG
