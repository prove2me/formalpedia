-- Prove2me | solution 1 for mme_stothers_phi134_pattern_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:25:12.870475+00:00
-- url     : https://prove2.me/submissions/142f178a-9969-4e04-a426-62b47f13a591

import Definitions.Def_mme_stothers_phi134_profile_data

open MME
open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem solution : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, cwSquareBlockType] at h0 h1 h2 ⊢
