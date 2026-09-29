-- Prove2me | Theorems.Thm_mme_released_recursive_level2_pen7
-- name    : mme_released_recursive_level2_pen7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T03:33:55.419655+00:00
-- url     : https://prove2.me/theorems/87938d34-dbcd-48a6-9c1c-e1a104eb774a
-- title:
--   Penalty bound for level-two regions 322 to 367
-- statement:
--   A uniform bound on the rational penalty expression for level-two regions 322 to 367.
--
--   For each region, the reference attached to a split is built from the same exponents that certify the
--   region's entropy, with the middle grade halved because a split weight is half its grade weight, and
--   with a negligible reference where the weight vanishes. The bound says the resulting rational
--   expression -- the total reference mass, minus two, plus the sum of squared weights over their
--   references -- is at most one part in fifty million, uniformly over these regions.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_level2_penalty_data
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_marginals
import Theorems.Thm_mme_released_recursive_level2_penalty_tools

open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level2_pen7 : ∀ j : Fin 46,
    ((∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨322 + j.val, by omega⟩),
        qvalQ (fun t ↦ ∑ i, PE ⟨322 + j.val, by omega⟩ i (c.val i) t)) - 2 +
      ∑ c : RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 ⟨322 + j.val, by omega⟩),
        (alphaQ ⟨322 + j.val, by omega⟩ c) ^ 2 /
          qvalQ (fun t ↦ ∑ i, PE ⟨322 + j.val, by omega⟩ i (c.val i) t)) ≤
      1/(5 * 10^7) := by sorry
