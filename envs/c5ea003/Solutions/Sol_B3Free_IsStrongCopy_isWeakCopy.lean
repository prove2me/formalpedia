-- Prove2me | solution 1 for B3Free.IsStrongCopy.isWeakCopy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:17:38.915025+00:00
-- url     : https://prove2.me/submissions/4c0b55e8-a0f6-4003-85fb-9769dd5e0366

import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
open B3Free Finset in
theorem solution {α : Type*} {P : Type*} [Preorder P] {ι : P → Finset α}
    (h : IsStrongCopy ι) : IsWeakCopy ι := by
  exact ⟨h.1, fun p q hpq => (h.2 p q).mpr hpq⟩
