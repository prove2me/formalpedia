-- Prove2me | solution 1 for IITTensorNetwork.schmidtRank_maxEnt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:51:34.840644+00:00
-- url     : https://prove2.me/submissions/3f8a04b8-4fd3-41f1-b385-ce814efe960d

-- Sol generated from Novelty/IITTensorNetworkSchmidt.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_IITTensorNetwork_rank_rhoLeft
import Theorems.Thm_IITTensorNetwork_rhoLeft_maxEntState

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











lemma rank_maxEntState (hu : Function.Injective u) (hv : Function.Injective v) {c : ℝ}
    (hc : c ≠ 0) : schmidtRank (maxEntState c u v) = Fintype.card γ := by
  have h := rank_rhoLeft (maxEntState c u v)
  rw [rhoLeft_maxEntState hu hv c, Matrix.rank_diagonal, Fintype.card_subtype] at h
  rw [← h]
  have hfilter : (Finset.univ.filter
      (fun f : α => ((if f ∈ Finset.image u Finset.univ then c ^ 2 else 0 : ℝ) : ℂ) ≠ 0))
      = Finset.image u Finset.univ := by
    ext f
    by_cases hmem : f ∈ Finset.image u Finset.univ <;>
      simp [hmem, hc, pow_eq_zero_iff]
  rw [hfilter, Finset.card_image_of_injective _ hu, Finset.card_univ]








open IITTensorNetwork in
theorem solution(hu : Function.Injective u) (hv : Function.Injective v)
    (hγ : 0 < Fintype.card γ) : schmidtRank (maxEnt u v) = Fintype.card γ := by
  have hpos : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast hγ
  refine rank_maxEntState hu hv ?_
  positivity
