-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_natural_word_trivial_iff
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.natural_word_trivial_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:20.514217+00:00
-- url     : https://prove2.me/theorems/54db742d-6af4-4256-8cfe-6741fb5bb593
-- title:
--   Computable Presentations: natural word trivial iff
-- statement:
--   The Computable Presentations construction uses the natural word trivial iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L71-L92
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L71-L92

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.natural_word_trivial_iff (p : PresentationCode) (hp : WellFormed p)
    (w : List (ℕ × Bool)) (hw : ∀ letter ∈ w, letter.1 < p.1) :
    FreeGroup.mk w ∈ Subgroup.normalClosure {r | r ∈ naturalRelators p} ↔
      PresentedGroup.mk (relations p) (interpretWord p.1 w) = 1 := by sorry
