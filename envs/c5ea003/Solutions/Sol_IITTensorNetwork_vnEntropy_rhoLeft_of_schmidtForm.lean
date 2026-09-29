-- Prove2me | solution 1 for IITTensorNetwork.vnEntropy_rhoLeft_of_schmidtForm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:47.901541+00:00
-- url     : https://prove2.me/submissions/c885ccad-f6f9-4d15-b164-980715935c34

-- Sol generated from Novelty/IITTensorNetworkWeightedGHZ.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ
import Theorems.Thm_IITTensorNetwork_roots_charpoly_diagonal
import Theorems.Thm_IITTensorNetwork_vnEntropy_eq_multiset_sum

/-! # Schmidt form, weighted GHZ chains, and the exact value of `Φ`

This file completes the analysis of the mission conjecture "`Φ` is determined by
the Schmidt rank" by exhibiting, for every chain length `n ≥ 2` and every local
dimension `d`, a one-parameter family of matrix product states of *fixed* bond
dimension and *fixed* Schmidt rank `d` at every cut whose integrated information
sweeps out the whole interval `(0, 2 log d]`.

The tool is the *Schmidt form* of a bipartite pure state: a factorization

`M = L · diag(w) · Rᴴ`  with  `Lᴴ L = 1`,  `Rᴴ R = 1`,

i.e. an isometric change of basis on both sides bringing the state to diagonal
form with Schmidt coefficients `w`.  Main structural results:

* `vnEntropy_rhoLeft_of_schmidtForm`, `vnEntropy_rhoRight_of_schmidtForm`,
  `mutualInformation_of_schmidtForm` : the marginal entropies, and hence the
  mutual information across the cut, are the Shannon entropy of the squared
  Schmidt coefficients — *only the Schmidt spectrum matters*;
* `normalized_of_schmidtForm` : normalization is `∑ w² = 1`;
* `schmidtRank_of_schmidtForm` : the Schmidt rank is the number of Schmidt
  coefficients (when all are nonzero).

These are then applied to the **weighted GHZ chain state**
`ψ_w = ∑ₓ wₓ |x x ⋯ x⟩`, whose cut matrix is computed exactly
(`chainCutMatrix_weightedGhz`).  Consequences:

* `phi_weightedGhz` : `Φ(ψ_w) = 2 ∑ₓ -wₓ² log wₓ²` for every `n ≥ 2`;
* `schmidtRank_chainCutMatrix_weightedGhz` : the Schmidt rank at every cut is
  `d`, independently of `w`;
* `phi_unbalancedGhz_eq_two_mul_binEntropy` and
  `phi_unbalancedGhz_lt_two_log_two` : for `d = 2` the value is
  `2 H₂(c²)`, which is *strictly* below `2 log 2 = 2 log (Schmidt rank)`
  precisely when `c² ≠ 1/2`, while the state remains a bond-dimension-two MPS of
  Schmidt rank two at every bipartition.

Together with `phi_ghz` (the flat case) this settles the status of the
conjecture: `Φ` is bounded by, but not determined by, the Schmidt rank, and
equals `2 log (Schmidt rank)` exactly on flat spectra.
-/

open Finset Matrix Polynomial
open scoped ComplexOrder

open IITTensorNetwork

/-! ## States in Schmidt form -/


variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]










/-! ## The weighted GHZ chain state -/


variable {n d : ℕ} {w : Fin d → ℝ}













/-! ## The unbalanced GHZ family at `d = 2` -/


variable {n : ℕ}









open IITTensorNetwork in
omit [DecidableEq β] in
theorem solution{M : Matrix α β ℂ} {L : Matrix α γ ℂ}
    {R : Matrix β γ ℂ} {w : γ → ℝ} (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1)
    (hM : M = L * Matrix.diagonal (fun k => (w k : ℂ)) * Rᴴ)
    (hcard : Fintype.card γ ≤ Fintype.card α) :
    vnEntropy (rhoLeft M) = ∑ k, Real.negMulLog (w k ^ 2) := by
  classical
  set D : Matrix γ γ ℂ := Matrix.diagonal (fun k => (w k : ℂ)) with hD
  set D2 : Matrix γ γ ℂ := Matrix.diagonal (fun k => ((w k ^ 2 : ℝ) : ℂ)) with hD2
  have hDD : D * Dᴴ = D2 := by
    rw [hD, hD2, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    simp [Complex.conj_ofReal, sq]
  have hrho : rhoLeft M = L * (D2 * Lᴴ) := by
    have hexp : rhoLeft M = L * (D * (Rᴴ * R) * Dᴴ) * Lᴴ := by
      rw [rhoLeft, hM]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hexp, hR, Matrix.mul_one, hDD, Matrix.mul_assoc]
  have hne : (X : ℂ[X]) ^ (Fintype.card α - Fintype.card γ) * D2.charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic D2).ne_zero
  have hcp : (rhoLeft M).charpoly = X ^ (Fintype.card α - Fintype.card γ) * D2.charpoly := by
    rw [hrho, Matrix.charpoly_mul_comm_of_le L (D2 * Lᴴ) hcard]
    congr 2
    rw [Matrix.mul_assoc, hL, Matrix.mul_one]
  have hroots : (rhoLeft M).charpoly.roots
      = Multiset.replicate (Fintype.card α - Fintype.card γ) 0 + D2.charpoly.roots := by
    rw [hcp, Polynomial.roots_mul (hcp ▸ hne), Polynomial.roots_pow, Polynomial.roots_X,
      Multiset.nsmul_singleton]
  rw [vnEntropy_eq_multiset_sum (rhoLeft_posSemidef M).isHermitian, hroots,
    Multiset.map_add, Multiset.sum_add, Multiset.map_replicate]
  rw [hD2, roots_charpoly_diagonal, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  simp [Multiset.sum_replicate, -Complex.ofReal_pow]
