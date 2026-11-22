-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.continuous_coverScore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:04:33.841199+00:00
-- url     : https://prove2.me/submissions/94e1ebfa-30e5-42f1-ab8d-2fc91a7c41bf

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_continuous_supportScore

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (supports : Supports n) :
    Continuous (coverScore supports) := by
  induction supports with
  | nil => exact continuous_const
  | cons support rest ih => exact (continuous_supportScore support).max ih
end Kourovka.MetabelianEnumeration.ConeVerifier
