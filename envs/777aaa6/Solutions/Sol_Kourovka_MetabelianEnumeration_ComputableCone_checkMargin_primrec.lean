-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.checkMargin_primrec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:12:50.115384+00:00
-- url     : https://prove2.me/submissions/4b6bc9f1-417b-4202-99c5-54f35316d2e4

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_badDirection_primrec

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution : Primrec₂ checkMargin := Primrec.not.comp badDirection_primrec
end Kourovka.MetabelianEnumeration.ComputableCone
