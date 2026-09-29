-- Prove2me | solution 1 for B3Free.WeakFree.mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:32:14.163708+00:00
-- url     : https://prove2.me/submissions/ace259a0-e0e5-49b7-9da5-c2d9ad43eda1

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
open B3Free Finset in
theorem solution {α : Type*} {F G : Finset (Finset α)} {P : Type*} [Preorder P]
    (h : WeakFree G P) (hFG : F ⊆ G) : WeakFree F P := by
  rintro ⟨ι, hcopy, hmem⟩
  exact h ⟨ι, hcopy, fun p => hFG (hmem p)⟩
