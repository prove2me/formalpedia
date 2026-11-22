-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_inverseCheck
-- name    : Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_inverseCheck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:44.370017+00:00
-- url     : https://prove2.me/theorems/d9767d29-c09a-4023-97c5-324181bbd658
-- title:
--   Natural Word Substitution: interpret inverse Check
-- statement:
--   The Natural Word Substitution construction uses the interpret inverse Check property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L105-L111
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L105-L111

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations

theorem Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_inverseCheck (n m : ℕ) (f g : Images) (hf : WellFormed (m, f))
    (i : ℕ) (hi : i < n) :
    interpretWord n (substitute g (f.getD i []) ++ [(i, false)]) =
      FreeGroup.lift (fun j : Fin m => interpretWord n (g.getD j.val []))
        (interpretWord m (f.getD i [])) * (FreeGroup.of ⟨i, hi⟩)⁻¹ := by sorry
