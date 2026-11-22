-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:44:47.512639+00:00
-- url     : https://prove2.me/submissions/422e23e0-5d72-4186-8356-fdf0cebed92a

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution (z : ℤ) : |unitSign z| = 1 := by
  unfold unitSign; split <;> norm_num
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
