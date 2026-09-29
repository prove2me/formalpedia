-- Prove2me | Definitions.Def_mme_certified_generic_floor_data
-- name    : mme_certified_generic_floor_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-23T05:02:18.168979+00:00
-- url     : https://prove2.me/theorems/71a0df00-a3bc-46b7-84df-2f620f8af035
-- title:
--   The rational floor a reference table assigns to a distribution
-- statement:
--   The rational lower bound that a table of reference exponents assigns to a rational distribution: the quadratic part of the Gibbs bound, minus each logarithm coefficient evaluated at the endpoint of its certified enclosure chosen by the coefficient's sign.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

namespace MME.Cert

/-- The rational floor a reference table assigns to a rational distribution. -/
noncomputable def regFloorG {W : Type u} [Fintype W] (p : W → ℚ) (e : W → Fin 4 → ℤ) : ℚ :=
  (∑ w, (p w - (p w) ^ 2 / qvalQ (e w))) -
    ∑ j, (if 0 ≤ (∑ w, p w * ((e w j : ℤ) : ℚ)) then
            (∑ w, p w * ((e w j : ℤ) : ℚ)) * logHi j
          else (∑ w, p w * ((e w j : ℤ) : ℚ)) * logLo j)

end MME.Cert


