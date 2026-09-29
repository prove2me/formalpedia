-- Prove2me | Definitions.Def_mme_released_recursive_level2_sum_data
-- name    : mme_released_recursive_level2_sum_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-23T01:26:46.429293+00:00
-- url     : https://prove2.me/theorems/6247bd94-d5d6-4dcf-b2d9-9ef3eb56573b
-- title:
--   Per-mode certificate tables for the level-two potentials
-- statement:
--   Per-mode certificate tables for the level-two potentials: the floor numerator and the reference exponent table a region contributes to a given mode, taken from the region's own certificate when that mode is the parametric one and from the uniform reference otherwise.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert
open scoped Classical
set_option autoImplicit false

namespace MME.L2Cert

/-- The per-region floor numerator of a mode, over `10 ^ 30`. -/
def gTab (i : Fin 3) (r : Fin 1104) : Int :=
  if certMode r = i then certNum r else 693147180559945309417232 * 10 ^ 6

/-- The per-region exponent table of a mode. -/
def ETab (i : Fin 3) (r : Fin 1104) : Fin 3 → Fin 4 → Int :=
  if certMode r = i then certE r else Eunif

end MME.L2Cert


