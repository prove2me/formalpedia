-- Prove2me | Theorems.Thm_mme_regional_prescribed_profile_card
-- name    : mme_regional_prescribed_profile_card
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:33:49.281372+00:00
-- url     : https://prove2.me/theorems/4e15e960-56ba-41aa-a9d3-9b0b17d76411
-- title:
--   Exact count of dependent regional joint profiles
-- statement:
--   For independent parent components with different finite split alphabets, count all addresses realizing their exact integer joint profiles as the product of the corresponding multinomials.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign. Supporting result for https://arxiv.org/html/2404.16349v2#S6 . This result alone is not the regional extraction theorem or a numerical omega certificate.

import Definitions.Def_mme_regional_entropy_rate_data
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_region_count_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RegionRealization MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false

theorem mme_regional_prescribed_profile_card {R : Type*} [Fintype R] {A : R → Type*} [∀ r, Fintype (A r)]
    (n : R → ℕ) (mu : ∀ r, A r → ℕ) (hm : ∀ r, ∑ a, mu r a = n r) :
    Fintype.card {w : ∀ r, Fin (n r) → A r // ∀ r a, count (w r) a = mu r a} =
      ∏ r, (n r).factorial / ∏ a, (mu r a).factorial := by sorry
