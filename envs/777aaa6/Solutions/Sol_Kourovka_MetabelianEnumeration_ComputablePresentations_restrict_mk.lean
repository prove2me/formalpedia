-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.restrict_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:43:36.293229+00:00
-- url     : https://prove2.me/submissions/2fc5843e-58a3-4049-8fe2-87b7c6ea2fb7

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution (n : ℕ) (w : List (ℕ × Bool)) :
    restrictGenerators n (FreeGroup.mk w) = interpretWord n w := by
  rw [restrictGenerators, FreeGroup.lift_mk]
  unfold interpretWord
  congr 1
  apply List.map_congr_left
  intro letter _
  split <;> cases letter.2 <;> simp_all
end Kourovka.MetabelianEnumeration.ComputablePresentations
