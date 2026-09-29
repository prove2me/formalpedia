-- Prove2me | solution 1 for IITTensorNetwork.mutualInformation_eq_zero_iff_schmidtRank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:47:43.425986+00:00
-- url     : https://prove2.me/submissions/f40a0887-6687-4604-88b4-989d1bdaedc0

-- Sol generated from Novelty/IITTensorNetworkSchmidt.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_IITTensorNetwork_rank_rhoLeft
import Theorems.Thm_IITTensorNetwork_rank_rhoRight
import Theorems.Thm_IITTensorNetwork_vnEntropy_eq_zero_iff_rank_eq_one
import Theorems.Thm_IITTensorNetwork_vnEntropy_nonneg

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





variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] {u : γ → α} {v : γ → β}



















open IITTensorNetwork in
theorem solution{M : Matrix α β ℂ}
    (hM : Normalized M) : mutualInformation M = 0 ↔ schmidtRank M = 1 := by
  have h1 := vnEntropy_eq_zero_iff_rank_eq_one (rhoLeft_posSemidef M) (rhoLeft_trace hM)
  have h2 := vnEntropy_eq_zero_iff_rank_eq_one (rhoRight_posSemidef M) (rhoRight_trace hM)
  rw [rank_rhoLeft] at h1
  rw [rank_rhoRight] at h2
  have hn1 : 0 ≤ vnEntropy (rhoLeft M) :=
    vnEntropy_nonneg (rhoLeft_posSemidef M) (rhoLeft_trace hM)
  have hn2 : 0 ≤ vnEntropy (rhoRight M) :=
    vnEntropy_nonneg (rhoRight_posSemidef M) (rhoRight_trace hM)
  constructor
  · intro h
    have : vnEntropy (rhoLeft M) = 0 := by
      simp only [mutualInformation] at h
      linarith
    exact h1.mp this
  · intro h
    simp only [mutualInformation, h1.mpr h, h2.mpr h, add_zero]
