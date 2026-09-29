-- Prove2me | solution 1 for mme_stothers_phi125_block_certificate_of_profile_extraction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T06:53:51.183468+00:00
-- url     : https://prove2.me/submissions/098bc90b-0961-4847-ae8d-38094f2aeb81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_stothers_phi125_finite_block_extraction_from_profile_v3

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
              (1 - b)))
    (hprofile :
      ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
        Tendsto s atTop atTop ∧
        Tendsto loss atTop (nhds 0) ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ (k : ℕ) (x y z : Fin k → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun i ↦ MMObj K (x i) (y i) (z i)))
              ((cyclicSymmetrization
                (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
                  (s n)) ∧
            V ^ (s n) * (1 - loss n) ≤
              ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau)) :
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
  exact mme_stothers_phi125_finite_block_extraction_from_profile_v3
    tau a b V hV hVlt hprofile
