-- Prove2me | solution 1 for IITTensorNetwork.schmidtRank_of_schmidtForm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:47.26014+00:00
-- url     : https://prove2.me/submissions/202add6e-d52e-46f6-a710-898d857f3f32

-- Sol generated from Novelty/IITTensorNetworkWeightedGHZ.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
import Definitions.Def_Novelty_IITTensorNetworkWeightedGHZ

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
omit [DecidableEq α] [DecidableEq β] in
theorem solution{M : Matrix α β ℂ} {L : Matrix α γ ℂ} {R : Matrix β γ ℂ}
    {w : γ → ℝ} (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1)
    (hM : M = L * Matrix.diagonal (fun k => (w k : ℂ)) * Rᴴ) (hw : ∀ x, w x ≠ 0) :
    schmidtRank M = Fintype.card γ := by
  refine le_antisymm ?_ ?_
  · calc schmidtRank M = (L * Matrix.diagonal (fun k => (w k : ℂ)) * Rᴴ).rank := by
          rw [schmidtRank, hM]
      _ ≤ (L * Matrix.diagonal (fun k => (w k : ℂ))).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card γ := Matrix.rank_le_card_width _
  · have hprod : Lᴴ * M * R = Matrix.diagonal (fun k => (w k : ℂ)) := by
      rw [hM]
      calc Lᴴ * (L * Matrix.diagonal (fun k => (w k : ℂ)) * Rᴴ) * R
          = (Lᴴ * L) * Matrix.diagonal (fun k => (w k : ℂ)) * (Rᴴ * R) := by
            simp [Matrix.mul_assoc]
        _ = Matrix.diagonal (fun k => (w k : ℂ)) := by rw [hL, hR]; simp
    have hrankD : (Matrix.diagonal (fun k => (w k : ℂ))).rank = Fintype.card γ := by
      rw [Matrix.rank_diagonal, Fintype.card_subtype]
      rw [Finset.filter_true_of_mem (fun x _ => by
        simpa [Complex.ofReal_eq_zero] using hw x), Finset.card_univ]
    calc Fintype.card γ = (Lᴴ * M * R).rank := by rw [hprod, hrankD]
      _ ≤ M.rank := le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
