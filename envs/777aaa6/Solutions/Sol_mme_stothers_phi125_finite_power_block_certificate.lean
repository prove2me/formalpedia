-- Prove2me | solution 1 for mme_stothers_phi125_finite_power_block_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T00:58:49.295408+00:00
-- url     : https://prove2.me/submissions/beb61287-57ad-4e54-a7e6-49300d5c50ad

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_stothers_phi125_block_certificate_of_profile_extraction
import Theorems.Thm_mme_stothers_phi125_profile_cofinal_finite_extraction

open MME BigOperators Filter

universe u
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (tau a b : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        4 / MME.StothersFourth.H 6 tau *
          ((MME.StothersFourth.L 6 tau / a) ^ a *
            ((MME.StothersFourth.E 6 tau *
              MME.StothersFourth.H 6 tau) / (1 - a)) ^ (1 - a)) *
          ((MME.StothersFourth.L 6 tau / b) ^ b *
            ((2 * MME.StothersFourth.H 6 tau) / (1 - b)) ^
              (1 - b))) :
    ∃ (N alpha beta gamma : ℕ),
      0 < N ∧ alpha + beta + gamma = N ∧
      ∃ (kept : Finset
          (MME.StothersFourth.Phi125.CyclicExactEdge
            N alpha beta gamma))
        (block : kept → TensorObj K 3) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦
            MME.StothersFourth.Phi125.cyclicModeWord e.1 i)) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j : Fin kept.card ↦
            block (kept.equivFin.symm j)))
          ((cyclicSymmetrization
            (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
              (2 * N)) ∧
        0 ≤ B ∧
        (∀ e : kept, ∀ W : ℝ,
          0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) ∧
        V ^ (2 * N) < (kept.card : ℝ) * B := by
  exact mme_stothers_phi125_block_certificate_of_profile_extraction
    tau a b htauLower htauUpper ha hb hab V hV hVlt
    (mme_stothers_phi125_profile_cofinal_finite_extraction
      tau a b htauLower htauUpper ha hb hab V hV hVlt)

