-- Prove2me | Definitions.Def_mme_certified_generic_rate_data
-- name    : mme_certified_generic_rate_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-23T05:16:24.163271+00:00
-- url     : https://prove2.me/theorems/643a9337-d7af-4c58-a985-874f91b602d6
-- title:
--   The normalized split distribution of a region
-- statement:
--   The normalized split distribution of a region: the weight of a split divided by the region's size.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_thin_split_data

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.Cert

/-- The normalized split distribution of a region. -/
noncomputable def alphaG {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (r : Fin R)
    (c : RecursiveThinSplit.Split half (parent r)) : ℚ := (m r c : ℚ) / (n r : ℚ)

end MME.Cert


