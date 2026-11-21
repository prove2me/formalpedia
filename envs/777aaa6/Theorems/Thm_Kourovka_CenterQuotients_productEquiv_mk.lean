-- Prove2me | Theorems.Thm_Kourovka_CenterQuotients_productEquiv_mk
-- name    : Kourovka.CenterQuotients.productEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:49.539453+00:00
-- url     : https://prove2.me/theorems/88046959-a7ed-4844-8655-2c828304c9c0
-- title:
--   Center Quotients: product Equiv mk
-- statement:
--   The Center Quotients construction uses the product Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterQuotients.lean#L89-L91
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterQuotients.lean#L89-L91

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_CenterQuotients
set_option autoImplicit true
open Kourovka
open Kourovka.CenterQuotients
variable {A B G H T : Type*} [Group A] [Group B] [Group G] [Group H] [Group T]

theorem Kourovka.CenterQuotients.productEquiv_mk (a : A) (b : B) :
    productEquiv (QuotientGroup.mk a, QuotientGroup.mk b) = QuotientGroup.mk (a, b) := by sorry
