-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverBounds.conjugate_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:59:34.277626+00:00
-- url     : https://prove2.me/submissions/c562b9fc-98b3-48f2-b7cf-a21d29270e5a

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords
namespace Kourovka.MetabelianEnumeration.ComputableCoverBounds
theorem _root_.solution {n : ℕ} {x w : WordGroup} (hx : x ∈ bounded n)
    (hw : w ∈ bounded n) : FiniteCover.conjugate x w ∈ bounded n :=
  (bounded n).mul_mem ((bounded n).mul_mem ((bounded n).inv_mem hw) hx) hw
end Kourovka.MetabelianEnumeration.ComputableCoverBounds
