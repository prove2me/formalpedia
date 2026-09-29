-- Prove2me | Theorems.Thm_mme_stothers_phi116_profile_source_cyclic_value_below
-- name    : mme_stothers_phi116_profile_source_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:51:47.264567+00:00
-- url     : https://prove2.me/theorems/26d6024a-3d95-454e-b2a6-22a20aaa9ef3
-- title:
--   Cyclic tau-value of the common phi_116 exact-profile source
-- statement:
--   The common grouped tensor with phi_116 multiplicities (alpha,alpha,beta,beta) has cyclic tau-value at least every strict product of two coupled targets below L and two rectangular targets below E squared, with an explicit constant factor 1/16.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21; A. M. Davie and A. J. Stothers (2013), Lemma 5.1(i).

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_finite_kronFin_cyclic_value_product_below
import Theorems.Thm_mme_stothers_phi116_rectangular_component_cyclic_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_profile_source_cyclic_value_below
    {K : Type u} [Field K] (tau : ℝ)
    (htau : 2 ≤ 3 * tau)
    (alpha beta : ℕ)
    (W : Fin 4 → ℝ)
    (hWpos : ∀ r, 0 < W r)
    (hWcoupled : W 0 < MME.StothersFourth.L 6 tau ∧ W 1 < MME.StothersFourth.L 6 tau)
    (hWrect : W 2 < MME.StothersFourth.E 6 tau ^ (2 : ℕ) ∧ W 3 < MME.StothersFourth.E 6 tau ^ (2 : ℕ)) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 4 (fun r ↦
          (MME.StothersFourth.Phi116.phi116ComponentObj K r).kronPow
            (MME.StothersFourth.Phi116.phi116ComponentMultiplicity alpha beta r)))) tau
      (∏ r : Fin 4, (W r ^ MME.StothersFourth.Phi116.phi116ComponentMultiplicity alpha beta r) / 2) := by
  sorry
