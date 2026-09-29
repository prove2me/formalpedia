-- Prove2me | solution 1 for mme_stothers_phi116_outer_hashing_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:13:44.785221+00:00
-- url     : https://prove2.me/submissions/e78fb097-5d63-4250-b933-3c431536f9de

import Theorems.Thm_mme_stothers_phi116_exact_address_component_factorization
import Theorems.Thm_mme_stothers_phi116_outer_hashing_value_of_exact_address_factorization

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (_hsupport :
      ∀ sigma : Fin 3 → Fin 3,
        sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
        sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
        (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockTensor sigma = 0)
    (_hcomponents :
      TensorObj.Restrict (MMObj K 12 1 12)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![0, 1, 2]) ∧
        TensorObj.Restrict (MMObj K 12 1 12)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![1, 0, 2]) ∧
        TensorObj.Restrict (coupledObj K 6)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![0, 0, 0]) ∧
        TensorObj.Restrict (coupledObj K 6)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![1, 1, 1])) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 5 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  apply mme_stothers_phi116_outer_hashing_value_of_exact_address_factorization
    tau htauLower htauUpper
  intro N alpha beta hsum address
  exact mme_stothers_phi116_exact_address_component_factorization
    hsum address
