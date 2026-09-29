-- Prove2me | solution 1 for IITTensorNetwork.rhoLeft_maxEntState
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:49:51.660479+00:00
-- url     : https://prove2.me/submissions/dee88fef-ed5e-47bc-bdbd-d9f414984e50

-- Sol generated from Novelty/IITTensorNetworkSchmidt.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_IITTensorNetwork_isoMatrix_conjTranspose_mul
import Theorems.Thm_IITTensorNetwork_isoMatrix_mul_conjTranspose

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







omit [Fintype α] [Fintype β] [DecidableEq γ] in
lemma conjTranspose_maxEntState (c : ℝ) (u : γ → α) (v : γ → β) :
    (maxEntState c u v)ᴴ = maxEntState c v u := by
  simp [maxEntState, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]












open IITTensorNetwork in
omit [Fintype α] in
theorem solution(hu : Function.Injective u) (hv : Function.Injective v) (c : ℝ) :
    rhoLeft (maxEntState c u v)
      = Matrix.diagonal
          (fun f => ((if f ∈ Finset.image u Finset.univ then c ^ 2 else 0 : ℝ) : ℂ)) := by
  have hmul : isoMatrix u * (isoMatrix v)ᴴ * (isoMatrix v * (isoMatrix u)ᴴ)
      = isoMatrix u * ((isoMatrix v)ᴴ * isoMatrix v) * (isoMatrix u)ᴴ := by
    simp [Matrix.mul_assoc]
  rw [rhoLeft, conjTranspose_maxEntState, maxEntState, maxEntState, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hmul, isoMatrix_conjTranspose_mul hv, Matrix.mul_one,
    isoMatrix_mul_conjTranspose hu]
  ext f f'
  by_cases hff : f = f'
  · subst hff
    by_cases hmem : f ∈ Finset.image u Finset.univ <;>
      simp [sq, apply_ite (fun x : ℝ => (x : ℂ))]
  · simp [hff]
