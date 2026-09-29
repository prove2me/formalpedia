-- Prove2me | solution 1 for IITTensorNetwork.mutualInformation_eq_two_mul_entanglementEntropy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:46:02.80192+00:00
-- url     : https://prove2.me/submissions/38fbe403-a302-41da-a198-81b455286c93

-- Sol generated from Novelty/IITTensorNetworkSchmidt.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_IITTensorNetwork_vnEntropy_eq_multiset_sum

/-! # Bipartite pure states, Schmidt rank and quantum mutual information

A pure state of a bipartite quantum system `A ⊗ B` with finite local index sets
`α` and `β` is encoded by its coefficient matrix `M : Matrix α β ℂ`, normalized
by `∑ i j, ‖M i j‖ ^ 2 = 1`.  The two reduced density matrices are `M * Mᴴ`
(on `A`) and `Mᴴ * M` (on `B`), the *Schmidt rank* across the cut is the rank of
`M`, and, since the global state is pure, the quantum mutual information across
the cut is

`I(A : B) = S(ρ_A) + S(ρ_B) - S(ρ_AB) = S(ρ_A) + S(ρ_B)`.

Main results:

* `rhoLeft_trace`, `rhoRight_trace` : the reduced matrices are density matrices;
* `schmidtRank_pos` : the Schmidt rank of a normalized state is at least one;
* `mutualInformation_nonneg`;
* `mutualInformation_le_two_log_schmidtRank` : the mutual information across a
  cut is at most `2 log (Schmidt rank)`;
* `mutualInformation_eq_zero_iff_schmidtRank_eq_one` : the mutual information
  vanishes exactly for product states across the cut;
* `vnEntropy_rhoLeft_eq_rhoRight` : the two marginal entropies of a pure state
  agree (equal-dimension parts), so `I(A : B) = 2 S(ρ_A)`;
* `mutualInformation_flat` : a flat Schmidt spectrum of rank `r` gives
  `I(A : B) = 2 log r`, the maximum allowed by the Schmidt rank.
-/

open Finset Matrix
open scoped ComplexOrder

open IITTensorNetwork


variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]





















variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Marginal entropies of a pure state agree.**  For a bipartite pure state
whose two parts have the same index type, the entropy of the left marginal
equals the entropy of the right marginal. -/
theorem vnEntropy_rhoLeft_eq_rhoRight (M : Matrix α α ℂ) :
    vnEntropy (rhoLeft M) = vnEntropy (rhoRight M) := by
  rw [vnEntropy_eq_multiset_sum (rhoLeft_posSemidef M).isHermitian,
    vnEntropy_eq_multiset_sum (rhoRight_posSemidef M).isHermitian]
  congr 2
  exact congrArg Polynomial.roots (Matrix.charpoly_mul_comm M Mᴴ)




variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] {u : γ → α} {v : γ → β}



















open IITTensorNetwork in
theorem solution(M : Matrix α α ℂ) :
    mutualInformation M = 2 * entanglementEntropy M := by
  rw [mutualInformation, entanglementEntropy, ← vnEntropy_rhoLeft_eq_rhoRight M]
  ring
