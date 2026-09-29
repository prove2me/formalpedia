-- Prove2me | Theorems.Thm_mme_stothers_phi125_finite_block_extraction_from_profile_v2
-- name    : mme_stothers_phi125_finite_block_extraction_from_profile_v2
-- status  : Open
-- author  : @WillR
-- created : 2026-09-05T06:44:51.1493+00:00
-- url     : https://prove2.me/theorems/a03e7669-f3c1-4bdb-afd9-3cc3dbe472d7
-- title:
--   Finite Phi125 block extraction from a profile witness
-- statement:
--   A reusable finite block-extraction interface for the phi125 constituent, isolating the combinatorial conversion of a cofinal profile witness into mode-distinct finite blocks with a strict tau-value surplus.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Section 5, Lemma 5.1; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi125_profile_data
import Definitions.Def_mme_tau_value

open MME BigOperators Filter
universe u
set_option autoImplicit false

theorem mme_stothers_phi125_finite_block_extraction_from_profile_v2
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
