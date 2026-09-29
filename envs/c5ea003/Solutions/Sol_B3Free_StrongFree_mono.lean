-- Prove2me | solution 1 for B3Free.StrongFree.mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:13:49.166534+00:00
-- url     : https://prove2.me/submissions/b4a593d5-d5a6-4301-b489-337d3cb177bb

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
open B3Free in
theorem solution {α : Type*} {F G : Finset (Finset α)} {P : Type*} [Preorder P]
    (h : StrongFree G P) (hFG : F ⊆ G) : StrongFree F P := by
  rintro ⟨ι, hι, hmem⟩
  exact h ⟨ι, hι, fun p => hFG (hmem p)⟩
