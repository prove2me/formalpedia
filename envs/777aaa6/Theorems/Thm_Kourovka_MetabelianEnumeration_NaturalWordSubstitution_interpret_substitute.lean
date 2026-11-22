-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_substitute
-- name    : Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_substitute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:44:11.334222+00:00
-- url     : https://prove2.me/theorems/ffb22a38-0497-499b-8dee-3a346e577524
-- title:
--   Natural Word Substitution: interpret substitute
-- statement:
--   The Natural Word Substitution construction uses the interpret substitute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L48-L62
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean#L48-L62

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations

theorem Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_substitute (n m : ℕ) (f : Images) (w : Word) (hw : ValidWord n w) :
    interpretWord m (substitute f w) =
      FreeGroup.lift (fun i : Fin n => interpretWord m (f.getD i.val [])) (interpretWord n w) := by sorry
