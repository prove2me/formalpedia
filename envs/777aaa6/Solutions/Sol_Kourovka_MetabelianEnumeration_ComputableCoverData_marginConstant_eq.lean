-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverData.marginConstant_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:07:40.709799+00:00
-- url     : https://prove2.me/submissions/f31d28ef-0417-4555-adf6-fc99ab1efce5

import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Covers_ComputableCoverData

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverData
open ComputableIntegers FiniteCover
namespace Kourovka.MetabelianEnumeration.ComputableCoverData
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    marginConstant k r = (1 / 2 : ℚ) ^ r / k := by
  have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℚ) < k := by linarith
  apply min_eq_left
  apply (div_le_one hk0).mpr
  exact (pow_le_one₀ (by norm_num) (by norm_num) : (1 / 2 : ℚ) ^ r ≤ 1).trans hk1
end Kourovka.MetabelianEnumeration.ComputableCoverData
