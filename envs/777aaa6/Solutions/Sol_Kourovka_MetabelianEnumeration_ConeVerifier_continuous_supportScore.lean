-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ConeVerifier.continuous_supportScore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:30.274679+00:00
-- url     : https://prove2.me/submissions/f6300c7c-90b5-4e8a-9e0e-9cab8aef110a

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_continuous_dot

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier
namespace Kourovka.MetabelianEnumeration.ConeVerifier
theorem _root_.solution {n : ℕ} (support : List (Vec n)) :
    Continuous (supportScore support) := by
  induction support with
  | nil => exact continuous_const
  | cons u rest ih => exact (continuous_dot u).min ih
end Kourovka.MetabelianEnumeration.ConeVerifier
