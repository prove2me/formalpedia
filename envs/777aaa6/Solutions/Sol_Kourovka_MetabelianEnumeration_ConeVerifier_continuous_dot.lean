-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.continuous_dot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:43.593073+00:00
-- url     : https://prove2.me/submissions/d2d7ee21-e984-499a-98f6-3ccdd2d592e2

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (u : Vec n) : Continuous (dot u) := by
  unfold dot
  fun_prop
end Kourovka.MetabelianEnumeration.ConeVerifier
