-- Prove2me | Theorems.Thm_mme_stothers_phi116_outer_hashing_value_of_support_and_components
-- name    : mme_stothers_phi116_outer_hashing_value_of_support_and_components
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T06:13:57.552551+00:00
-- url     : https://prove2.me/theorems/02dca208-9ab5-410a-a1dd-5b94bfcecf1b
-- title:
--   Outer hashing value from the four-edge support and component restrictions
-- statement:
--   This interface lemma isolates the analytic reduction used in the Φ₁₁₆ outer-hashing argument. For a field-valued fourth-power constituent, assume the grading is supported only on the four specified edge patterns and that the two outer and two diagonal component restrictions have their stated tensor forms. Under the admissible range 2 ≤ 3τ ≤ 3, every nonnegative threshold V below the class value at level 6, parameter τ, and index 5 is attained as a τ-value of the cyclically symmetrized constituent. The lemma is intended as a reusable reduction interface for the corresponding mission theorem.
-- source:
--   Mission Davie--Stothers Fourth-Power Bound, Phi116 outer-hashing reduction; formal interface matching theorem mme_stothers_phi116_outer_hashing_value.

import Definitions.Def_mme_stothers_phi116_outer_grading
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tensor_bridge
open MME
universe u

theorem mme_stothers_phi116_outer_hashing_value_of_support_and_components
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (hsupport :
      ∀ sigma : Fin 3 → Fin 3,
        sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
        sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
        (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockTensor sigma = 0)
    (hcomponents :
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
  sorry
