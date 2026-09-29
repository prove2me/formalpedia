-- Prove2me | solution 1 for BooleanValuedRealization.bval_ch_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T16:51:48.158812+00:00
-- url     : https://prove2.me/submissions/fb803aa1-ae8d-423d-834d-ae54099e2754

import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_ButtonsSwitches

open BooleanValuedRealization

variable {Btn Sw : Type*}

theorem solution (S : Finset Btn) (s : Sw) :
    bval (cassign (Btn := Btn) S) (chAtom s) ≠ ⊥ := by
  -- Unfolds to `{g | g s = true} ≠ ∅` on the power-set Boolean algebra.
  simp [bval, chAtom, cassign]
  refine Set.nonempty_iff_ne_empty.mp ?_
  exact ⟨fun _ => true, by simp⟩
