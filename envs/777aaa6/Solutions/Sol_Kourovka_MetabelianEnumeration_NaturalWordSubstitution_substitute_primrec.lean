-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.substitute_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:25.121263+00:00
-- url     : https://prove2.me/submissions/177c5f25-d9a3-4b68-a7bb-41ce478d9cdf

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableWords_invRev_primrec


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution : Primrec₂ substitute := by
  have hlookup : Primrec (fun p : (Images × Word) × (ℕ × Bool) => p.1.1.getD p.2.1 []) :=
    (Primrec.list_getD []).comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_flatMap Primrec.snd
    ((Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true))
      hlookup (invRev_primrec.comp hlookup)).to₂)
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
