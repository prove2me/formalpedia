-- Prove2me | solution 1 for mme_released_recursive_profile_counts_1_mode_1
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T16:57:39.719859+00:00
-- url     : https://prove2.me/submissions/cc3ec79e-8cd3-4490-bdb6-bdfe406ec487

import Definitions.Def_mme_released_recursive_profile_mixture
import Definitions.Def_mme_released_global_yz_word_data
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option profiler true

private theorem checked : ∀ (s : Fin 45) (v : Fin 81),
    ((jointRows 1 s).map (fun a ↦ if atom a.1 1 = ReleasedGlobalYZ.codeWord v then a.2 else 0)).sum =
      parentCount (term 1 s) (roles 1 1) (ReleasedGlobalYZ.codeWord v) := by
  intro s
  fin_cases s <;> decide +kernel

theorem solution : ∀ (s : Fin 45) (w : Word),
    ((jointRows 1 s).map (fun a ↦ if atom a.1 1 = w then a.2 else 0)).sum =
      parentCount (term 1 s) (roles 1 1) w := by
  intro s w
  obtain ⟨v, hv⟩ := ReleasedGlobalYZ.wordEquiv.surjective w
  have hcode : ReleasedGlobalYZ.codeWord v = w := hv
  exact hcode ▸ checked s v
