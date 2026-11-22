-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_include_interpret
-- name    : Kourovka.MetabelianEnumeration.ComputablePresentations.include_interpret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:09.286429+00:00
-- url     : https://prove2.me/theorems/c09aa72d-9d27-4ebf-8bfa-2aa56a67ea86
-- title:
--   Computable Presentations: include interpret
-- statement:
--   The Computable Presentations construction uses the include interpret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L47-L63
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputablePresentations.lean#L47-L63

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords

theorem Kourovka.MetabelianEnumeration.ComputablePresentations.include_interpret (n : ℕ) (w : List (ℕ × Bool))
    (hw : ∀ letter ∈ w, letter.1 < n) :
    includeGenerators n (interpretWord n w) = FreeGroup.mk w := by sorry
