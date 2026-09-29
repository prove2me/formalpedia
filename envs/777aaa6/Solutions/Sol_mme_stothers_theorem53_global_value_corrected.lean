-- Prove2me | solution 1 for mme_stothers_theorem53_global_value_corrected
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T18:21:41.250718+00:00
-- url     : https://prove2.me/submissions/00387a59-7fa8-4240-982d-bf1d91a17198

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_stothers_theorem53_slice_infimum_form
import Theorems.Thm_mme_stothers_lemma52_same_marginal

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
        (MME.StothersFourth.cwFourthObj K 6) tau V := by
  refine mme_stothers_theorem53_slice_infimum_form tau htauLower htauUpper a b
    ha hb.1 haPos hbPos hsame ?_
  intro c hc hcy
  exact mme_stothers_lemma52_same_marginal.2 c b hc hb hbPos hcy
