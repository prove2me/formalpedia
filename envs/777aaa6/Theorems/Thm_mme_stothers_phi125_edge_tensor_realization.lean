-- Prove2me | Theorems.Thm_mme_stothers_phi125_edge_tensor_realization
-- name    : mme_stothers_phi125_edge_tensor_realization
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-05T08:31:03.055388+00:00
-- url     : https://prove2.me/theorems/0c46f421-e697-4c88-b855-54b13e56e6c9
-- title:
--   Phi125 exact-edge tensor realization
-- statement:
--   For an exact symmetric phi125 profile and a finite set of cyclic exact edges with mode-word injectivity, realize the retained edges as tensor blocks whose direct sum restricts the corresponding even power of the cyclic phi125 constituent. Every block has the uniform local tau-value lower bound below the supplied budget. This isolates the tensor realization and local constituent-value step of the Davie--Stothers extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5, Lemma 5.1(ii), printed pp. 364-365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_phi125_edge_tensor_realization
    {K : Type u} [Field K]
    (tau : ℝ) (N alpha beta gamma : ℕ)
    (hN : 0 < N) (hprofile : alpha + beta + gamma = N)
    (kept : Finset
      (MME.StothersFourth.Phi125.CyclicExactEdge N alpha beta gamma))
    (B : ℝ) (hB : 0 ≤ B)
    (hinjective :
      ∀ i : Fin 3,
        Function.Injective (fun e : kept ↦
          MME.StothersFourth.Phi125.cyclicModeWord e.1 i)) :
    ∃ (block : kept → TensorObj K 3),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j : Fin kept.card ↦
          block (kept.equivFin.symm j)))
        ((cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
            (2 * N)) ∧
      (∀ e : kept, ∀ W : ℝ,
        0 ≤ W → W < B → HasTauValueAtLeast (block e) tau W) := by
  sorry
