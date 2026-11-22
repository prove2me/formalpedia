-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.coneCheck_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:47.265965+00:00
-- url     : https://prove2.me/submissions/1069c0a4-ad22-4783-a173-3b888dfa08db

import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_checkMargin_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_coneCover_iff_cubeMargin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
open FourierMotzkin
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (supports : Supports n) :
    checkMargin supports 0 = true ↔ ConeCover supports :=
  (checkMargin_correct supports 0).trans (coneCover_iff_cubeMargin supports).symm
end Kourovka.MetabelianEnumeration.ConeVerifier
