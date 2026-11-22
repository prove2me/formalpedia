-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.upper_constraint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:16.993268+00:00
-- url     : https://prove2.me/submissions/43fecc5f-43af-4abd-b519-55a1307994f3

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b t : K} (ha : 0 < a) :
    a * t + b ≤ 0 ↔ t ≤ -b / a := by
  rw [le_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith
end Kourovka.MetabelianEnumeration.FourierMotzkin
