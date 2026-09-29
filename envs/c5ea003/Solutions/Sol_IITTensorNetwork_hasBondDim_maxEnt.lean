-- Prove2me | solution 1 for IITTensorNetwork.hasBondDim_maxEnt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:47:40.668168+00:00
-- url     : https://prove2.me/submissions/0c8b54ed-d9fc-4559-8d74-46c272ced3d9

-- Sol generated from Novelty/IITTensorNetworkMPS.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkSchmidt

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





omit [Fintype α] [Fintype β] in
/-- A maximally entangled state whose Schmidt vectors are labelled by `Fin χ`
has bond dimension `χ`. -/
theorem hasBondDim_maxEntState {χ : ℕ} (c : ℝ) (u : Fin χ → α) (v : Fin χ → β) :
    HasBondDim (maxEntState c u v) χ :=
  ⟨(c : ℂ) • isoMatrix u, (isoMatrix v)ᴴ, by rw [maxEntState, Matrix.smul_mul]⟩




variable {l m d χ : ℕ}













open IITTensorNetwork in
omit [Fintype α] [Fintype β] in
theorem solution{χ : ℕ} (u : Fin χ → α) (v : Fin χ → β) :
    HasBondDim (maxEnt u v) χ :=
  hasBondDim_maxEntState _ u v
