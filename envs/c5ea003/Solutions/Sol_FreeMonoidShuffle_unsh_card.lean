-- Prove2me | solution 1 for FreeMonoidShuffle.unsh_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:06:17.930335+00:00
-- url     : https://prove2.me/submissions/7d2a3229-8b5d-4d91-8f9c-0c52a650942c

import Mathlib
import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle

set_option maxHeartbeats 400000

open FreeMonoidShuffle Finset

open FreeMonoidShuffle in
/-- **The target, verbatim.** -/
theorem solution {X : Type*} (w : List X) : (unsh w).card = 2 ^ w.length := by
  -- `unsh (a :: w)` is two copies of `unsh w` under different maps, so the card doubles.
  induction w with
  | nil => simp [unsh]
  | cons a w ih => simp [unsh, ih, pow_succ]; ring
