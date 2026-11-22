-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.certifiedDelta_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:32.745215+00:00
-- url     : https://prove2.me/submissions/f0ba9973-668e-4299-bc20-bdcfdd723e4e

import Definitions.Def_Kourovka_Polyhedral_Radius
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
import Definitions.Def_Kourovka_Covers_CertifiedRadius

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover
namespace Kourovka.MetabelianEnumeration.FiniteCover
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {C : ℚ} (hC : 0 < C) :
    0 < certifiedDelta k C ∧ certifiedDelta k C ≤ C / 4 ∧
      certifiedDelta k C < 1 / (2 * (k : ℚ)) := by
  have hk' : (0 : ℚ) < k := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hk
  refine ⟨lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
  apply (min_le_right _ _).trans_lt
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith
end Kourovka.MetabelianEnumeration.FiniteCover
