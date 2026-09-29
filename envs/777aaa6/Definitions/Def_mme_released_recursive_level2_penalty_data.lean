-- Prove2me | Definitions.Def_mme_released_recursive_level2_penalty_data
-- name    : mme_released_recursive_level2_penalty_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-23T02:15:07.851553+00:00
-- url     : https://prove2.me/theorems/9d9d81c8-16a6-4cdd-a235-cd4acd9d7f8c
-- title:
--   Split distribution and penalty references of a level-two region
-- statement:
--   The normalized split distribution of a level-two region, and the penalty reference exponents of that region, taken from its entropy certificate with the middle grade halved and with a negligible reference where the weight vanishes.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false

namespace MME.L2Cert

/-- The normalized split distribution of a level-two region. -/
def alphaQ (r : Fin 1104) (c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r)) : ℚ :=
  (m2 r c : ℚ) / (n2 r : ℚ)

/-- The penalty reference exponents of a region, reused from its entropy certificate. -/
def PE (r : Fin 1104) (i : Fin 3) (a : Fin (2 * 2 ^ (1 - 1) + 1)) (k : Fin 4) : ℤ :=
  if i = certMode r then
    (if a.val = 1 then certE r 1 k - (if k.val = 0 then 1 else 0)
     else if (l2At r).2.2 = 0 then (if k.val = 0 then -100 else 0)
     else certE r 0 k)
  else 0

end MME.L2Cert


