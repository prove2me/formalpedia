-- Prove2me | solution 1 for mme_stothers_theorem53_slice_stationary_form
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-10T05:58:11.836504+00:00
-- url     : https://prove2.me/submissions/1d43efd8-c49b-4bf4-a146-e6f076db3c6b

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_general_profile_fourth_value_stationary_unconditional
import Theorems.Thm_mme_stothers_theorem53_rational_dense_rate

open MME

universe u

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false

theorem solution
    {K : Type u} [Field K]
    (tau : Real) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (a b : Fin 10 → Real)
    (ha : MME.StothersFourth.InZ a)
    (hb : MME.StothersFourth.InN b)
    (haPos : ∀ i : Fin 10, 0 < a i)
    (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i => a i - b i)) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau a a *
            (MME.StothersFourth.entropyProduct b /
              MME.StothersFourth.entropyProduct a) →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6) tau V := by
  intro V hV hVlt
  obtain ⟨base, bstar, hbase, hbstar, hmarg, hInN, hrate⟩ :=
    mme_stothers_theorem53_rational_dense_rate tau a b hb haPos hbPos hsame V hVlt
  exact mme_stothers_general_profile_fourth_value_stationary_unconditional
    base bstar tau htauLower htauUpper hbase hbstar hmarg hInN V hV hrate
