-- Prove2me | Definitions.Def_mme_certified_generic_ceiling_data
-- name    : mme_certified_generic_ceiling_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-23T05:08:11.458681+00:00
-- url     : https://prove2.me/theorems/3b1ac7d4-6cc8-4da1-b04d-203aec55698d
-- title:
--   The rational ceiling a reference table assigns to a distribution
-- statement:
--   The rational upper bound that a table of reference exponents assigns to a rational distribution: the total reference mass minus the total weight, minus each logarithm coefficient evaluated at the endpoint of its certified enclosure chosen by the coefficient's sign.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_region_count_entropy_data

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v

namespace MME.Cert

/-- The rational ceiling a reference table assigns to a rational distribution. -/
noncomputable def regCeilG {W : Type u} [Fintype W] (p : W → ℚ) (e : W → Fin 4 → ℤ) : ℚ :=
  (∑ w, (qvalQ (e w) - p w)) -
    ∑ j, (if 0 ≤ (∑ w, p w * ((e w j : ℤ) : ℚ)) then
            (∑ w, p w * ((e w j : ℤ) : ℚ)) * logLo j
          else (∑ w, p w * ((e w j : ℤ) : ℚ)) * logHi j)

end MME.Cert


