-- Prove2me | solution 1 for mme_stothers_phi233_pattern_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:56:39.621622+00:00
-- url     : https://prove2.me/submissions/0b3c7c7f-ed6a-48e6-ac71-34ec5ecee071

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_CW_square_five_grade_certificate

open MME

set_option autoImplicit false
set_option maxRecDepth 10000
set_option warningAsError true

theorem solution :
    Function.Injective MME.StothersFourth.Phi233.pattern := by
  have hcode : ∀ t : Fin 10,
      t.val + 1 =
        4 * (MME.StothersFourth.Phi233.pattern t (0 : Fin 3)).val +
          (MME.StothersFourth.Phi233.pattern t (1 : Fin 3)).val := by
    intro t
    fin_cases t <;> rfl
  intro r s hrs
  have h0 := congrArg Fin.val (congrFun hrs (0 : Fin 3))
  have h1 := congrArg Fin.val (congrFun hrs (1 : Fin 3))
  have hr := hcode r
  have hs := hcode s
  apply Fin.ext
  omega
