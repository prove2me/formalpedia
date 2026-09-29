-- Prove2me | Definitions.Def_mme_released_recursive_level2_uniform_data
-- name    : mme_released_recursive_level2_uniform_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T22:51:19.921444+00:00
-- url     : https://prove2.me/theorems/4413b854-a8cd-4e1f-aaf8-859da9141c45
-- title:
--   Reference table for a uniform level-two mode
-- statement:
--   The reference exponent table for a uniform level-two mode: one half on each of the two supported grades.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_certified_entropy_rational_data

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert
open scoped Classical
set_option autoImplicit false

namespace MME.L2Cert

/-- The exponent table for a uniform level-two mode: reference one half on each of the two
supported grades. -/
def Eunif : Fin 3 → Fin 4 → ℤ := fun a j ↦ if a.val ≠ 2 ∧ j.val = 0 then -1 else 0

end MME.L2Cert


