-- Prove2me | Theorems.Thm_mme_released_recursive_level2_floor_cases
-- name    : mme_released_recursive_level2_floor_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T22:51:55.716709+00:00
-- url     : https://prove2.me/theorems/6707c887-4b69-48cb-b1e1-9218c6cc91b7
-- title:
--   The two cases of a level-two grade distribution and its uniform floor
-- statement:
--   The two cases of a level-two grade distribution, and the certified logarithm constants as
--   explicit rationals.
--
--   In each region exactly one mode has parent grade two. In the other two modes the grade distribution
--   is the fair pair, one half on each of two grades, and its certified floor is exactly the certified
--   lower bound for the logarithm of two, whatever the region. In the parametric mode the distribution
--   is the region's weight parameter, the complementary middle weight, and the parameter again, each
--   over the scale.
--
--   Also recorded are the four certified logarithm enclosures as plain rational literals, which is what
--   any explicit arithmetic with them needs.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_marginals
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level2_floor_cases :
    (logLo 0 = 693147180559945309417232/10^24 ∧ logHi 0 = 693147180559945309417233/10^24 ∧
    logLo 1 = 1098612288668109691395245/10^24 ∧ logHi 1 = 1098612288668109691395246/10^24 ∧
    logLo 2 = 1609437912434100374600759/10^24 ∧ logHi 2 = 1609437912434100374600760/10^24 ∧
    logLo 3 = 1945910149055313305105352/10^24 ∧ logHi 3 = 1945910149055313305105353/10^24) ∧
    (∀ (i : Fin 3) (r : Fin 1104), ¬ parent2 r i = 2 →
      PG i r 0 = 1/2 ∧ PG i r 1 = 1/2 ∧ PG i r 2 = 0) ∧
    (∀ (i : Fin 3) (r : Fin 1104), ¬ parent2 r i = 2 → regFloor i r Eunif = logLo 0) ∧
    ∀ (i : Fin 3) (r : Fin 1104), parent2 r i = 2 →
      PG i r 0 = ((l2At r).2.2 : ℚ) / (D : ℚ) ∧
      PG i r 1 = ((D - 2 * (l2At r).2.2 : ℕ) : ℚ) / (D : ℚ) ∧
      PG i r 2 = ((l2At r).2.2 : ℚ) / (D : ℚ) := by sorry
