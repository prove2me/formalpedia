-- Prove2me | solution 1 for mme_stothers_theorem53_slice_infimum_form
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:16:41.037658+00:00
-- url     : https://prove2.me/submissions/938c9333-90d2-42de-8288-6f435382332e

import Theorems.Thm_mme_stothers_positive_slice_minimum_is_stationary
import Theorems.Thm_mme_stothers_theorem53_slice_stationary_form
import Definitions.Def_mme_stothers_fourth_data

open MME

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    (tau : Real) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (a b : Fin 10 → Real)
    (ha : MME.StothersFourth.InZ a)
    (hbZ : MME.StothersFourth.InZ b)
    (haPos : ∀ i : Fin 10, 0 < a i)
    (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : MME.StothersFourth.InY (fun i => a i - b i))
    (hmin : ∀ c : Fin 10 → Real, MME.StothersFourth.InZ c →
      MME.StothersFourth.InY (fun i => c i - b i) →
      MME.StothersFourth.entropyProduct b ≤ MME.StothersFourth.entropyProduct c) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.globalRate 6 tau a a *
            (MME.StothersFourth.entropyProduct b /
              MME.StothersFourth.entropyProduct a) →
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6) tau V := by
  exact mme_stothers_theorem53_slice_stationary_form tau htauLower htauUpper a b ha
    (mme_stothers_positive_slice_minimum_is_stationary b hbZ hbPos hmin)
    haPos hbPos hsame