-- Prove2me | solution 2 for mme_stothers_theorem53_global_value_corrected
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-08T05:57:24.583823+00:00
-- url     : https://prove2.me/submissions/e7c3d7ac-058e-4767-8980-81501709932f

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_theorem53_slice_stationary_form

open MME

universe u

set_option autoImplicit false

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
        (MME.StothersFourth.cwFourthObj K 6) tau V :=
  mme_stothers_theorem53_slice_stationary_form tau htauLower htauUpper a b
    ha hb haPos hbPos hsame
