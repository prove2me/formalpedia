-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.lower_constraint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:11.507481+00:00
-- url     : https://prove2.me/submissions/e0899a15-ff63-4b5a-8015-1ccbab5d5ca1

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b t : K} (ha : a < 0) :
    a * t + b ≤ 0 ↔ -b / a ≤ t := by
  rw [div_le_iff_of_neg ha]
  constructor <;> intro h <;> nlinarith
end Kourovka.MetabelianEnumeration.FourierMotzkin
