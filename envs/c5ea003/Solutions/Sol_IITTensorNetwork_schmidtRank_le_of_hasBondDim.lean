-- Prove2me | solution 1 for IITTensorNetwork.schmidtRank_le_of_hasBondDim
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:58:45.710235+00:00
-- url     : https://prove2.me/submissions/e07369d4-b039-4ded-9a18-2d9be044b272

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









variable {l m d χ : ℕ}













open IITTensorNetwork in
omit [Fintype α] [DecidableEq α] [DecidableEq β] in
theorem solution{M : Matrix α β ℂ} {χ : ℕ} (h : HasBondDim M χ) :
    schmidtRank M ≤ χ := by
  obtain ⟨L, R, rfl⟩ := h
  calc (L * R).rank ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ Fintype.card (Fin χ) := Matrix.rank_le_card_width L
    _ = χ := Fintype.card_fin χ
