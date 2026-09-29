-- Prove2me | solution 1 for IITTensorNetwork.mutualInformation_le_two_log_bondDim
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:47:44.046981+00:00
-- url     : https://prove2.me/submissions/9bd0b1a8-f5aa-468d-b928-2e1891e0c97f

-- Sol generated from Novelty/IITTensorNetworkMPS.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_IITTensorNetwork_mutualInformation_le_two_log_schmidtRank
import Theorems.Thm_IITTensorNetwork_schmidtRank_le_of_hasBondDim
import Theorems.Thm_IITTensorNetwork_schmidtRank_pos

/-! # Bond dimension of matrix product states and the Schmidt rank bound

A tensor network state has *bond dimension at most `χ`* across a cut when its
coefficient matrix factors through a `χ`-dimensional auxiliary (virtual) space.
This is exactly the structure of a matrix product state (MPS) cut open at one
bond.  We prove:

* `schmidtRank_le_of_hasBondDim` : bond dimension bounds the Schmidt rank;
* `mutualInformation_le_two_log_bondDim` : hence the quantum mutual information
  across the cut is at most `2 log χ`;
* `mpsCutMatrix_factorization` and `hasBondDim_mpsCutMatrix` : an explicit MPS
  built from local tensors of bond dimension `χ` has bond dimension `χ`;
* `mutualInformation_mps_bondDim_two_le` : for bond dimension `2`, the mutual
  information across the cut is at most `2 log 2 = log 4`, the value attained by
  a maximally entangled qubit pair.
-/

open Finset Matrix
open scoped ComplexOrder

open IITTensorNetwork


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]









variable {l m d χ : ℕ}













open IITTensorNetwork in
theorem solution{M : Matrix α β ℂ} {χ : ℕ}
    (hM : Normalized M) (h : HasBondDim M χ) :
    mutualInformation M ≤ 2 * Real.log χ := by
  have hrank := schmidtRank_le_of_hasBondDim h
  have hpos : 1 ≤ schmidtRank M := schmidtRank_pos hM
  have hlog : Real.log (schmidtRank M) ≤ Real.log χ := by
    apply Real.log_le_log
    · exact_mod_cast hpos
    · exact_mod_cast hrank
  have := mutualInformation_le_two_log_schmidtRank hM
  linarith
