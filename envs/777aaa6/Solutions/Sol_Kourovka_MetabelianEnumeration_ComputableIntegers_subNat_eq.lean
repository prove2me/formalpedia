-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableIntegers.subNat_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:35.979819+00:00
-- url     : https://prove2.me/submissions/deed0e85-9884-41a7-9226-d8affd74818c

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Computability_ComputableIntegers

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableIntegers
namespace Kourovka.MetabelianEnumeration.ComputableIntegers
theorem _root_.solution (m n : ℕ) : subNat m n = (m : ℤ) - n := by
  unfold subNat
  split <;> omega
end Kourovka.MetabelianEnumeration.ComputableIntegers
