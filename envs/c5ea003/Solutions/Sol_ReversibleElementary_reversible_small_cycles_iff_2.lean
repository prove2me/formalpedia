-- Prove2me | solution 2 for ReversibleElementary.reversible_small_cycles_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:01:24.944476+00:00
-- url     : https://prove2.me/submissions/1360a7ab-01ef-4db8-a378-7f0cbb472f10

import Mathlib
import Definitions.Def_Novelty_ReversibleElementary
open ReversibleElementary in
theorem solution (w : Fin 256) :
    (ReversibleOn 1 w ∧ ReversibleOn 2 w ∧ ReversibleOn 3 w ∧ ReversibleOn 4 w) ↔
      w ∈ ([15, 51, 85, 170, 204, 240] : List (Fin 256)) := by
  revert w
  decide +kernel
