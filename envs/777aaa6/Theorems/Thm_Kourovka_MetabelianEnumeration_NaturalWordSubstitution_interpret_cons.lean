-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_cons
-- name    : Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:34.449373+00:00
-- url     : https://prove2.me/theorems/8b9d8cb6-f087-4d08-8488-c0c7b8afe33c
-- title:
--   Natural Word Substitution: interpret cons
-- statement:
--   The Natural Word Substitution construction uses the interpret cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L43-L46
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L43-L46

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations

theorem Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_cons (n : ℕ) (z : ℕ × Bool) (w : Word) (hz : z.1 < n) :
    interpretWord n (z :: w) =
      (if z.2 then FreeGroup.of ⟨z.1, hz⟩ else (FreeGroup.of ⟨z.1, hz⟩)⁻¹) *
        interpretWord n w := by sorry
