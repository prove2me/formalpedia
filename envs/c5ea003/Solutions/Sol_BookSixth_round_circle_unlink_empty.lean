-- Prove2me | solution 1 for BookSixth.round_circle_unlink_empty
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:20:45.101993+00:00
-- url     : https://prove2.me/submissions/6b05380d-06e2-4145-b344-ddc16ebe0486

import Definitions.Def_BookSixth

set_option autoImplicit false

open BookSixth

theorem solution : IsUnlink (fun _ : Fin 0 => (∅ : Set Space3)) := by
  refine ⟨fun _ => Homeomorph.refl Space3, ?_, ?_, ?_, ?_⟩
  · exact continuous_snd
  · exact continuous_snd
  · intro x
    rfl
  · intro i
    exact Fin.elim0 i
