-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverBounds.rightComm_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:22.594513+00:00
-- url     : https://prove2.me/submissions/89cd6eb7-633b-4201-880b-f0f0d60f40e9

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords
namespace Kourovka.MetabelianEnumeration.ComputableCoverBounds
theorem _root_.solution {n : ℕ} {x y : WordGroup} (hx : x ∈ bounded n)
    (hy : y ∈ bounded n) : FiniteCover.rightComm x y ∈ bounded n :=
  (bounded n).mul_mem ((bounded n).mul_mem
    ((bounded n).mul_mem ((bounded n).inv_mem hx) ((bounded n).inv_mem hy)) hx) hy
end Kourovka.MetabelianEnumeration.ComputableCoverBounds
