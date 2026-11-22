-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.map_normalClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:11.708413+00:00
-- url     : https://prove2.me/submissions/2ece695e-735c-42de-8360-7689db4982df

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution {G H : Type*} [Group G] [Group H]
    (f : G →* H) (S : Set G) (T : Set H)
    (h : ∀ r ∈ S, f r ∈ Subgroup.normalClosure T) {x : G}
    (hx : x ∈ Subgroup.normalClosure S) : f x ∈ Subgroup.normalClosure T := by
  exact Subgroup.normalClosure_le_normal (N := (Subgroup.normalClosure T).comap f) h hx
end Kourovka.MetabelianEnumeration.ComputablePresentations
