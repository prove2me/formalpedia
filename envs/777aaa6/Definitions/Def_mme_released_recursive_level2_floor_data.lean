-- Prove2me | Definitions.Def_mme_released_recursive_level2_floor_data
-- name    : mme_released_recursive_level2_floor_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T22:21:30.369718+00:00
-- url     : https://prove2.me/theorems/0db5824e-e594-4f6c-b9c2-611038715cf4
-- title:
--   Data for certified level-two entropy floors
-- statement:
--   Data for certified level-two entropy floors: a pair of one-letter words, the grade distribution of a region in one mode, and the rational floor a table of reference exponents assigns to that region.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_entropy_rational_data

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.L2Cert

/-- A pair of one-letter words. -/
def wpair (a b : Fin 3) : Fin 2 → CompleteSplit.CompleteWord 1 := ![fun _ ↦ a, fun _ ↦ b]

/-- The level-two grade distribution of a region in one mode. -/
noncomputable def PG (i : Fin 3) (r : Fin 1104) (a : Fin 3) : ℚ := (Jm r i a : ℚ) / (D : ℚ)

/-- The rational floor attached to a region by an exponent table. -/
noncomputable def regFloor (i : Fin 3) (r : Fin 1104) (E : Fin 3 → Fin 4 → ℤ) : ℚ :=
  (∑ a : Fin 3, (PG i r a - (PG i r a) ^ 2 / qvalQ (E a))) -
    ∑ j, (if 0 ≤ (∑ a : Fin 3, PG i r a * ((E a j : ℤ) : ℚ)) then
            (∑ a : Fin 3, PG i r a * ((E a j : ℤ) : ℚ)) * logHi j
          else (∑ a : Fin 3, PG i r a * ((E a j : ℤ) : ℚ)) * logLo j)

end MME.L2Cert


