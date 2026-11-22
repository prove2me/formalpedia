-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.any_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:24.419882+00:00
-- url     : https://prove2.me/submissions/9d7ce526-3f43-4c2c-a0c9-48fbc7ff1526

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).any (p a)) := by
  have h := Primrec.list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih => simp [List.foldr_cons, List.any_cons, ih]
end Kourovka.MetabelianEnumeration.ComputableCone
