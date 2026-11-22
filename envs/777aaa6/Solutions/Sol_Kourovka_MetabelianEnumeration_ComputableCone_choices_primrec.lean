-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.choices_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:57.685185+00:00
-- url     : https://prove2.me/submissions/c10925ee-316a-4953-b2e0-0f53f873b4aa

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_prependChoices_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec₂ choices := by
  have h := Primrec.list_foldr Primrec.snd (Primrec.const [[]])
    (prependChoices_primrec.comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro p
  induction p.2 with
  | nil => rfl
  | cons s rest ih => simp only [List.foldr_cons, choices, ← ih]; rfl
end Kourovka.MetabelianEnumeration.ComputableCone
