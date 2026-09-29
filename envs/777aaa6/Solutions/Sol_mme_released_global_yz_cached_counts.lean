-- Prove2me | solution 1 for mme_released_global_yz_cached_counts
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T13:50:34.104464+00:00
-- url     : https://prove2.me/submissions/3b1823b8-86f9-4863-9703-6aa403f24857

import Theorems.Thm_mme_released_global_yz_cached_counts_0
import Theorems.Thm_mme_released_global_yz_cached_counts_1
import Theorems.Thm_mme_released_global_yz_cached_counts_2
import Theorems.Thm_mme_released_global_yz_cached_counts_3
import Theorems.Thm_mme_released_global_yz_cached_counts_4
import Theorems.Thm_mme_released_global_yz_cached_counts_5
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalYZ
set_option autoImplicit false

theorem solution (o : Fin 6) (i : Fin 2) (s : Fin 45) (t : Fin 81) :
    cachedCounts o i s t =
      ((jointRows o s).map (fun a ↦ if atom a.1 (RecursiveYZ.yzMode i) = codeWord t then a.2 else 0)).sum := by
  fin_cases o
  · exact mme_released_global_yz_cached_counts_0 i s t
  · exact mme_released_global_yz_cached_counts_1 i s t
  · exact mme_released_global_yz_cached_counts_2 i s t
  · exact mme_released_global_yz_cached_counts_3 i s t
  · exact mme_released_global_yz_cached_counts_4 i s t
  · exact mme_released_global_yz_cached_counts_5 i s t
