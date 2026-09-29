-- Prove2me | solution 2 for ReversibleElementary.short_period_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:56:43.348915+00:00
-- url     : https://prove2.me/submissions/2ecf5a24-a2ae-407d-a92b-15ad25d5423c

import Mathlib
import Definitions.Def_Novelty_ReversibleElementary
open ReversibleElementary in
theorem solution (w : Fin 256)
    (hw : w ∉ ([15, 51, 85, 170, 204, 240] : List (Fin 256))) :
    ∃ n ∈ ({1, 2, 3, 4} : Finset ℕ), ¬ ReversibleOn n w := by
  revert w
  decide +kernel
