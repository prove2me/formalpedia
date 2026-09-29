-- Prove2me | solution 1 for B3Free.WeakFree.strongFree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:27:44.460728+00:00
-- url     : https://prove2.me/submissions/78caa65e-7b1c-476e-b6f0-e73ce558347a

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
open B3Free Finset in
theorem solution {α : Type*} {F : Finset (Finset α)} {P : Type*} [Preorder P]
    (h : WeakFree F P) : StrongFree F P := by
  rintro ⟨ι, hcopy, hmem⟩
  exact h ⟨ι, ⟨hcopy.1, fun p q hpq => (hcopy.2 p q).mpr hpq⟩, hmem⟩
