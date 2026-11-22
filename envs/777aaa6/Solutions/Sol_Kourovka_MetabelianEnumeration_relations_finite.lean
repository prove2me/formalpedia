-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.relations_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:45.115716+00:00
-- url     : https://prove2.me/submissions/24620da7-7d7a-4723-98b5-5a566faab39a

import Definitions.Def_Kourovka_Computability_Enumeration
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic
import Definitions.Def_Kourovka_Presentations_Presentations

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration
namespace Kourovka.MetabelianEnumeration
theorem _root_.solution (p : PresentationCode) : (relations p).Finite :=
  List.finite_toSet _
end Kourovka.MetabelianEnumeration
