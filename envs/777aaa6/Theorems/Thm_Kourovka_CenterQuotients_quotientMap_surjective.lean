-- Prove2me | Theorems.Thm_Kourovka_CenterQuotients_quotientMap_surjective
-- name    : Kourovka.CenterQuotients.quotientMap_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:01.702402+00:00
-- url     : https://prove2.me/theorems/2034cf29-96b7-4987-8445-021c30136341
-- title:
--   Center Quotients: quotient Map surjective
-- statement:
--   The Center Quotients construction uses the quotient Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterQuotients.lean#L34-L39
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterQuotients.lean#L34-L39

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_CenterQuotients
set_option autoImplicit true
open Kourovka
open Kourovka.CenterQuotients
variable {A B G H T : Type*} [Group A] [Group B] [Group G] [Group H] [Group T]

theorem Kourovka.CenterQuotients.quotientMap_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (quotientMap f hf) := by sorry
