-- Prove2me | Theorems.Thm_IITTensorNetwork_hasBondDim_maxEnt
-- name    : IITTensorNetwork.hasBondDim_maxEnt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:05:55.436323+00:00
-- url     : https://prove2.me/theorems/0b7204ee-6dab-4e72-90c4-3a9b3d179a63
-- title:
--   The canonical maximally entangled state of Schmidt rank `χ` has bond
-- statement:
--   The canonical maximally entangled state of Schmidt rank `χ` has bond
--   dimension `χ`.
--
--   ```lean
--   theorem IITTensorNetwork.hasBondDim_maxEnt{χ : ℕ} (u : Fin χ → α) (v : Fin χ → β) :
--       HasBondDim (maxEnt u v) χ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IITTensorNetworkMPS.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IITTensorNetworkMPS.lean#L72

-- Thm stub generated from Novelty/IITTensorNetworkMPS.lean
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

theorem IITTensorNetwork.hasBondDim_maxEnt{χ : ℕ} (u : Fin χ → α) (v : Fin χ → β) :
    HasBondDim (maxEnt u v) χ := by sorry
