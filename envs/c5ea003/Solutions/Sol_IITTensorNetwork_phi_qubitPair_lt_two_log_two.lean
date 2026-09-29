-- Prove2me | solution 1 for IITTensorNetwork.phi_qubitPair_lt_two_log_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T10:57:11.090984+00:00
-- url     : https://prove2.me/submissions/13607543-76ba-42a2-8d47-57ea1a0602c8

-- Sol generated from Novelty/IITTensorNetworkSchmidtSpectrum.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkEquality
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
import Theorems.Thm_IITTensorNetwork_chainCutMatrix_qubitPairState
import Theorems.Thm_IITTensorNetwork_mutualInformation_eq_two_mul_entanglementEntropy
import Theorems.Thm_IITTensorNetwork_phi_two_sites
import Theorems.Thm_IITTensorNetwork_qubitPairState_normalized
import Theorems.Thm_IITTensorNetwork_sum_negMulLog_lt_log_card
import Theorems.Thm_IITTensorNetwork_vnEntropy_diagonal

/-! # Schmidt-diagonal states and the failure of "Φ = 2 log (Schmidt rank)"

The mission conjecture in its naive reading — that the integrated information of
a tensor network state is determined by its Schmidt rank — is *false*: the
mutual information across a cut depends on the whole Schmidt spectrum, not just
on the number of nonzero Schmidt coefficients.  The Schmidt rank only provides
the upper bound `2 log (Schmidt rank)` proved in the companion files, and the
bound is attained exactly at a flat spectrum (`IITTensorNetworkEquality`).

This file provides the explicit witness.  We work with states given in Schmidt
form: a real vector `v` of Schmidt coefficients yields the coefficient matrix
`schmidtDiag v = diagonal v`, for which everything is computable:

* `normalized_schmidtDiag_iff` : normalization is `∑ v i ^ 2 = 1`;
* `mutualInformation_schmidtDiag` : `I = 2 ∑ -v i² log (v i²)`;
* `schmidtRank_schmidtDiag` : the Schmidt rank is the number of nonzero
  coefficients;
* `mutualInformation_schmidtDiag_lt_of_not_flat` /
  `mutualInformation_schmidtDiag_of_flat` : the sharp dichotomy against the
  bound `2 log (card)`.

We then instantiate this with a one-parameter family of two-qubit states
`qubitPairState c s = c|00⟩ + s|11⟩` (a matrix product state of bond dimension
two) and prove:

* `phi_qubitPair` : `Φ = 2(-c² log c² - s² log s²)`;
* `schmidtRank_qubitPair` : the Schmidt rank is `2` whenever `c, s ≠ 0`;
* `phi_qubitPair_lt_two_log_two` : as soon as `c² ≠ 1/2` the integrated
  information is *strictly* below `2 log 2 = 2 log (Schmidt rank)`, so `Φ` is
  not a function of the Schmidt rank;
* `phi_bellPair` : at `c = s = 1/√2` the value `2 log 2` is attained, so the
  bound is sharp — the bond-dimension-two cap `Φ ≤ 2 log 2` of
  `mutualInformation_mps_bondDim_two_le` is exactly the Bell/GHZ value.
-/

open Finset Matrix
open scoped ComplexOrder

open IITTensorNetwork

/-! ## States in Schmidt-diagonal form -/


variable {α : Type*} [Fintype α] [DecidableEq α]


/-- The left marginal of a Schmidt-diagonal state is diagonal with the squared
Schmidt coefficients on the diagonal. -/
lemma rhoLeft_schmidtDiag (v : α → ℝ) :
    rhoLeft (schmidtDiag v) = Matrix.diagonal (fun i => ((v i ^ 2 : ℝ) : ℂ)) := by
  rw [rhoLeft, schmidtDiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [Complex.conj_ofReal, sq]


/-- The entanglement entropy of a Schmidt-diagonal state is the Shannon entropy
of the squared Schmidt coefficients. -/
lemma vnEntropy_rhoLeft_schmidtDiag (v : α → ℝ) :
    vnEntropy (rhoLeft (schmidtDiag v)) = ∑ i, Real.negMulLog (v i ^ 2) := by
  rw [rhoLeft_schmidtDiag, vnEntropy_diagonal]

/-- The quantum mutual information of a Schmidt-diagonal state. -/
lemma mutualInformation_schmidtDiag (v : α → ℝ) :
    mutualInformation (schmidtDiag v) = 2 * ∑ i, Real.negMulLog (v i ^ 2) := by
  rw [mutualInformation_eq_two_mul_entanglementEntropy, entanglementEntropy,
    vnEntropy_rhoLeft_schmidtDiag]



/-- **A non-flat Schmidt spectrum falls strictly below the rank bound.** -/
theorem mutualInformation_schmidtDiag_lt_of_not_flat {v : α → ℝ} (hv : ∑ i, v i ^ 2 = 1)
    (hne : ∃ i, v i ^ 2 ≠ ((Fintype.card α : ℝ))⁻¹) :
    mutualInformation (schmidtDiag v) < 2 * Real.log (Fintype.card α) := by
  have h := sum_negMulLog_lt_log_card (p := fun i => v i ^ 2) (fun i => sq_nonneg _) hv hne
  rw [mutualInformation_schmidtDiag]
  linarith



/-! ## Integrated information of a two-site chain -/


variable {d : ℕ} {psi : (Fin 2 → Fin d) → ℂ}



/-! ## The two-qubit family `c|00⟩ + s|11⟩` -/




lemma card_one_site : Fintype.card (Fin 1 → Fin 2) = 2 := by simp

/-- Sums over the configurations of one qubit. -/
lemma sum_one_site (F : (Fin 1 → Fin 2) → ℝ) :
    ∑ f, F f = F (fun _ => 0) + F (fun _ => 1) := by
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 2)).symm, Fin.sum_univ_two]
  rfl









open IITTensorNetwork in
theorem solution{c s : ℝ} (h : c ^ 2 + s ^ 2 = 1)
    (hne : c ^ 2 ≠ (2 : ℝ)⁻¹) :
    Phi (qubitPairState_normalized h) (le_refl 2) < 2 * Real.log 2 := by
  have hcoeff : ∑ f, qubitPairCoeff c s f ^ 2 = 1 := by
    rw [sum_one_site]
    norm_num [qubitPairCoeff]
    exact h
  have hexists : ∃ f, qubitPairCoeff c s f ^ 2
      ≠ ((Fintype.card (Fin 1 → Fin 2) : ℝ))⁻¹ := by
    refine ⟨fun _ => 0, ?_⟩
    rw [card_one_site]
    simpa [qubitPairCoeff] using hne
  have hlt := mutualInformation_schmidtDiag_lt_of_not_flat hcoeff hexists
  rw [card_one_site] at hlt
  rw [phi_two_sites, chainCutMatrix_qubitPairState]
  exact_mod_cast hlt
