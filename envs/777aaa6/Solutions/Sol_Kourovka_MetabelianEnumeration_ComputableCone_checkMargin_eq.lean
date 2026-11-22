-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.checkMargin_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:56.74677+00:00
-- url     : https://prove2.me/submissions/e3f7f6d6-c43f-4fd8-80e4-362aadfadd01

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_badDirection_eq

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (nr : ℕ × ℕ) (supports : SupportsCode) :
    checkMargin nr supports =
      ConeVerifier.checkMargin (decodeSupports nr.1 supports) ((1 / 2 : ℚ) ^ nr.2) := by
  rw [checkMargin, ConeVerifier.checkMargin, badDirection_eq]
end Kourovka.MetabelianEnumeration.ComputableCone
