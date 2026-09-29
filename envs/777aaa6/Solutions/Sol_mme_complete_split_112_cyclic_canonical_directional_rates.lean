-- Prove2me | solution 1 for mme_complete_split_112_cyclic_canonical_directional_rates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:48:47.556838+00:00
-- url     : https://prove2.me/submissions/9be3dd0c-d41e-408c-b557-6219b369a522

import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_permutation
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_mme_complete_split_112_parametric_canonical_directional_rates
import Theorems.Thm_mme_complete_split_CW_square_cyclic_profile_transport

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

/-- One actual family simultaneously supplies the original 112 source and both
cyclically oriented canonical complete-profile sources. -/
theorem solution (l g : ℕ) (hbalance : 341 * l < 100 * g) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (profileProbability ((l : ℚ) / (2 * ((l + g : ℕ) : ℚ))) mode sigma : ℝ)) ∧
      ∀ delta : ℝ, 0 < delta →
        ∀ᶠ m : ℕ in atTop,
          let N : ℕ := (l + g) * m
          let L : ℕ := l * m
          let G : ℕ := g * m
          ∃ A H : ℕ, ∃ family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            ((2 * N : ℕ) : ℝ) *
                (Real.log 2 * mme_modern_entropyBits (beta 2).probability - delta) ≤
              Real.log (A : ℝ) ∧
            ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
              Real.log ((A : ℝ) * (H : ℝ)) ∧
            Real.log ((5 ^ (2 * G) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (g : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 ∧
            Real.log ((5 ^ (2 * L) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (l : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 ∧
            ∀ (K : Type u) [Field K] (epsilon : ℝ≥0),
              (TensorObj.Restrict
                  (TensorObj.bigAdd (starObj (grading K 5) family))
                  (restrictedCanonicalPower K 5 beta epsilon (2 * N)) ∧
                ∀ a : Fin A,
                  (∀ sigma : Fin 3 → Fin (H + 1),
                    sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
                      (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
                  ∀ h : Fin H,
                    TensorObj.Isomorphic
                      (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G)))
                      ((starGrading (grading K 5) family a).blockSubtensor
                        (cTensorOneHOneAddress H h))) ∧
              ∀ (e : Equiv.Perm (Fin 3)),
                e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm →
                  TensorObj.Restrict
                    (TensorObj.permObj e
                      (TensorObj.bigAdd (starObj (grading K 5) family)))
                    (CompleteSplitCanonicalSquare.restrictedPower K 5
                      (fun i ↦ cwSquareBlockType 1 1 2 (e.symm i))
                      (fun i ↦ beta (e.symm i)) epsilon (2 * N)) ∧
                  ∀ (a : Fin A) (h : Fin H),
                    TensorObj.Isomorphic
                      (TensorObj.permObj e
                        (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G))))
                      (TensorObj.permObj e
                        ((starGrading (grading K 5) family a).blockSubtensor
                          (cTensorOneHOneAddress H h))) := by
  obtain ⟨beta, hbeta, hrates⟩ :=
    mme_complete_split_112_parametric_canonical_directional_rates.{u} l g hbalance
  refine ⟨beta, hbeta, ?_⟩
  intro delta hdelta
  filter_upwards [hrates delta hdelta] with m hm
  obtain ⟨A, H, family, hA, hH, houter, hjoint, hG, hL, htensor⟩ := hm
  refine ⟨A, H, family, hA, hH, houter, hjoint, hG, hL, ?_⟩
  intro K instK epsilon
  obtain ⟨hsource, hblocks⟩ := htensor K epsilon
  refine ⟨⟨hsource, hblocks⟩, ?_⟩
  intro e he
  have hcanonical := mme_complete_split_CW_square_cyclic_profile_transport
    K 5 (cwSquareBlockType 1 1 2) e he beta epsilon (2 * ((l + g) * m))
  refine ⟨?_, ?_⟩
  · exact (TensorObj.permObj_restrict e hsource).trans hcanonical.2
  · intro a h
    exact TensorObj.permObj_isomorphic e ((hblocks a).2 h)
