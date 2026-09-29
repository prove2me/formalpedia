-- Prove2me | solution 1 for mme_cyclic_kron_two_strict_below_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-04T05:38:33.892801+00:00
-- url     : https://prove2.me/submissions/670bff77-791c-426d-8b71-b42f5ba28206

import Mathlib.Tactic
import Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

universe u

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (A B : TensorObj K 3) (tau endpointA endpointB : ℝ)
    (hendpointA : 0 < endpointA) (hendpointB : 0 < endpointB)
    (hA : ∀ V : ℝ, 0 ≤ V → V < endpointA →
      HasTauValueAtLeast (cyclicSymmetrization A) tau V)
    (hB : ∀ V : ℝ, 0 ≤ V → V < endpointB →
      HasTauValueAtLeast (cyclicSymmetrization B) tau V)
    (V : ℝ) (hV : 0 ≤ V) (hVlt : V < endpointA * endpointB) :
    HasTauValueAtLeast
      (cyclicSymmetrization (TensorObj.kron A B)) tau V := by
  let factor : Fin 2 → TensorObj K 3 := ![A, B]
  let endpoint : Fin 2 → ℝ := ![endpointA, endpointB]
  have hproduct : HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 2
          (fun i ↦ (factor i).kronPow 1))) tau V := by
    apply mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
      factor (fun _ ↦ 1) tau endpoint
    · intro i
      fin_cases i
      · exact hendpointA
      · exact hendpointB
    · intro i W hW hWlt
      fin_cases i
      · exact hA W hW (by simpa [endpoint] using hWlt)
      · exact hB W hW (by simpa [endpoint] using hWlt)
    · exact hV
    · simpa [endpoint, Fin.prod_univ_succ] using hVlt
  have hiso : TensorObj.Isomorphic
      (TensorObj.kronFin 2 (fun i ↦ (factor i).kronPow 1))
      (TensorObj.kron A B) := by
    rw [← TensorQ.toQ_eq_iff]
    rw [mme_toQ_kronFin, TensorQ.toQ_kron]
    simp [factor, Fin.prod_univ_succ, TensorQ.toQ_kronPow]
  have hcyclic : TensorObj.Restrict
      (cyclicSymmetrization
        (TensorObj.kronFin 2 (fun i ↦ (factor i).kronPow 1)))
      (cyclicSymmetrization (TensorObj.kron A B)) :=
    mme_cyclicSymmetrization_mono_restrict hiso.1
  exact mme_HasTauValueAtLeast_mono_restrict hcyclic hproduct
