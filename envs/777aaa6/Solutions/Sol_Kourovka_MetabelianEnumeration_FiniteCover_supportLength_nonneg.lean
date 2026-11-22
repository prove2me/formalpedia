-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.supportLength_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:06:30.457743+00:00
-- url     : https://prove2.me/submissions/493ac891-0509-4a2d-a306-8ba8c3d01f21

import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Modules_TamenessCompactness
import Definitions.Def_Kourovka_Covers_CoverMargin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
open Collection ConeVerifier TamenessCompactness
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k : ℕ} (v : Lattice k) : 0 ≤ supportLength v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _
end Kourovka.MetabelianEnumeration.FiniteCover
