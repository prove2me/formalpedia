-- Prove2me | Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
-- name    : Kourovka_Certificates_NaturalWordSubstitution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:43:07.237583+00:00
-- url     : https://prove2.me/theorems/e321becc-020e-4333-ac4c-e8f4449e08e2
-- title:
--   Natural Word Substitution
-- statement:
--   Definitions and structural lemmas for Natural Word Substitution, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Certificates/NaturalWordSubstitution.lean

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
abbrev Word := List (ℕ × Bool)
abbrev Images := List Word
def substitute (f : Images) (w : Word) : Word :=
  w.flatMap fun z => if z.2 then f.getD z.1 [] else FreeGroup.invRev (f.getD z.1 [])
def ValidWord (n : ℕ) (w : Word) : Prop := ∀ z ∈ w, z.1 < n
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution


