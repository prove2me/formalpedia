-- Prove2me | solution 1 for Kourovka.CenterQuotients.productEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:31:58.615402+00:00
-- url     : https://prove2.me/submissions/952ca054-cca6-44a7-9cf2-8db9b23cb96e

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_CenterQuotients

set_option autoImplicit true
open Kourovka
open Kourovka.CenterQuotients
variable {A B G H T : Type*} [Group A] [Group B] [Group G] [Group H] [Group T]
namespace Kourovka.CenterQuotients
theorem _root_.solution (a : A) (b : B) :
    productEquiv (QuotientGroup.mk a, QuotientGroup.mk b) = QuotientGroup.mk (a, b) :=
  quotientProduct_mk a b
end Kourovka.CenterQuotients
