-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.feasible_eliminate_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:37.67449+00:00
-- url     : https://prove2.me/submissions/c28e720f-73b1-466d-9c44-cc422b90874d

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_elimination_step

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {n : ℕ} (rows : List (Row (n + 1)))
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Feasible (eliminate rows) K ↔ Feasible rows K := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ := (elimination_step rows x).mp hx
    exact ⟨Fin.cons t x, ht⟩
  · rintro ⟨x, hx⟩
    refine ⟨Fin.tail x, (elimination_step rows (Fin.tail x)).mpr ⟨x 0, ?_⟩⟩
    simpa only [Fin.cons_self_tail] using hx
end Kourovka.MetabelianEnumeration.FourierMotzkin
