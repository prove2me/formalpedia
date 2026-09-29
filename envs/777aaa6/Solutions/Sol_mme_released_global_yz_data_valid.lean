-- Prove2me | solution 1 for mme_released_global_yz_data_valid
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:17:16.271463+00:00
-- url     : https://prove2.me/submissions/a1929827-45fd-4bd2-9ad7-adcd09bc96ab

import Definitions.Def_mme_released_global_yz_certificate
import Theorems.Thm_mme_released_global_yz_cached_counts
import Theorems.Thm_mme_released_global_yz_expression_data
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ MME.ReleasedGlobalNumeric
set_option autoImplicit false

theorem solution :
    (∀ o i s t, cachedCounts o i s t =
      ((jointRows o s).map (fun a ↦ if atom a.1 (RecursiveYZ.yzMode i) = codeWord t then a.2 else 0)).sum) ∧
    (∀ o i, (entries o i).map Prod.fst = prune (rawTerms o i)) ∧
    (∀ o i, rateFloor o ≤ totalBound o i) := by
  exact ⟨mme_released_global_yz_cached_counts,mme_released_global_yz_expression_data⟩
