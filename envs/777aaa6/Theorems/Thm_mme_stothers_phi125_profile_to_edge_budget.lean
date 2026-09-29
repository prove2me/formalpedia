-- Prove2me | Theorems.Thm_mme_stothers_phi125_profile_to_edge_budget
-- name    : mme_stothers_phi125_profile_to_edge_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T08:30:53.850758+00:00
-- url     : https://prove2.me/theorems/7ff1f35a-b975-45e4-a080-3453877d7440
-- title:
--   Phi125 profile extraction to a mode-distinct edge budget
-- statement:
--   From a cofinal finite profile witness below the Davie--Stothers two-parameter rate, extract a positive tensor power, an exact symmetric profile, and a finite set of cyclic exact edges with injective mode words. The edge budget is nonnegative and strictly exceeds the target value raised to the selected even power. This is the type-2 hashing and collision-pruning component of Lemma 5.1(ii), separated from tensor realization.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5, Lemma 5.1(ii), printed pp. 364-365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi125_profile_to_edge_budget
    {K : Type u} [Field K] (tau a b : ℝ)
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
            N alpha beta gamma)) (B : ℝ),
        (∀ i : Fin 3,
          Function.Injective (fun e : kept ↦
            MME.StothersFourth.Phi125.cyclicModeWord e.1 i)) ∧
        0 ≤ B ∧ V ^ (2 * N) < (kept.card : ℝ) * B := by
  sorry
