-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.pair_constraint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:21.242861+00:00
-- url     : https://prove2.me/submissions/548543a3-3d42-482e-992d-afb2b8cef446

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b c d : K} (ha : a < 0) (hc : 0 < c) :
    c * b - a * d ≤ 0 ↔ -b / a ≤ -d / c := by
  have hrewrite : -b / a = b / -a := by ring
  rw [hrewrite, div_le_div_iff₀ (neg_pos.mpr ha) hc]
  constructor <;> intro h <;> nlinarith
end Kourovka.MetabelianEnumeration.FourierMotzkin
