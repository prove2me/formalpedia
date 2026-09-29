-- Prove2me | solution 1 for FreeMonoidShuffle.unsh_cons
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T00:57:12.499008+00:00
-- url     : https://prove2.me/submissions/541c04b1-873a-4d8a-8b37-c15e41ca23ec

import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle

open FreeMonoidShuffle

open FreeMonoidShuffle in
/-- **The defining recursion of the unshuffle coproduct**: unshuffling `a :: w` places
the letter `a` at the front of either the left or the right half of each unshuffle of `w`. -/
theorem solution {X : Type*} (a : X) (w : List X) :
    unsh (a :: w) = ((unsh w).map (fun p => (a :: p.1, p.2))) +
      ((unsh w).map (fun p => (p.1, a :: p.2))) := by
  rfl
