-- Prove2me | Theorems.Thm_mme_stothers_phi125_block_certificate_of_profile_extraction
-- name    : mme_stothers_phi125_block_certificate_of_profile_extraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T00:56:40.293743+00:00
-- url     : https://prove2.me/theorems/8b596425-6d6c-43ea-8953-9fef8c0391b7
-- title:
--   Phi125 finite block certificate from cofinal profile extraction
-- statement:
--   A source-faithful conversion interface for the literal $\phi_{125}$ constituent: assuming the cofinal finite profile extraction at a value $V$ below the displayed two-parameter rate, construct one finite power block with injective mode words, a uniform local tau-value budget, and total weighted rank strictly exceeding $V^{2N}$. This isolates the finite extraction and collision-free certificate step from the asymptotic profile lemma.
-- source:
--   Davie--Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5, Lemma 5.1(ii), with the finite-power block interface made explicit.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi125_block_certificate_of_profile_extraction
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
  sorry
