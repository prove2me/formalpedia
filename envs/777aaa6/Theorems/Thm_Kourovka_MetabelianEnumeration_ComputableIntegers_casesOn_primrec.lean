-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIntegers_casesOn_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableIntegers.casesOn_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:43:50.311067+00:00
-- url     : https://prove2.me/theorems/70028eed-f37a-46ad-ab0f-df1fbc0f24da
-- title:
--   Computable Integers: cases On primrec
-- statement:
--   The Computable Integers construction uses the cases On primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L25-L30
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableIntegers.lean#L25-L30

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers

theorem Kourovka.MetabelianEnumeration.ComputableIntegers.casesOn_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β}
    (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a)) := by sorry
