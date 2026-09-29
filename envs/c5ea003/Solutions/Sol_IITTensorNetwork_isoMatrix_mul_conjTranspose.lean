-- Prove2me | solution 1 for IITTensorNetwork.isoMatrix_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:47:42.231483+00:00
-- url     : https://prove2.me/submissions/6ffa25b1-63e9-4e94-95fb-5a69bd0c5ca9

-- Sol generated from Novelty/IITTensorNetworkSchmidt.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkSchmidt

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
omit [Fintype α] [DecidableEq γ] in
theorem solution(hu : Function.Injective u) :
    isoMatrix u * (isoMatrix u)ᴴ
      = Matrix.diagonal (fun f => if f ∈ Finset.image u Finset.univ then (1 : ℂ) else 0) := by
  ext f f'
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hff : f = f'
  · subst hff
    rw [if_pos rfl]
    by_cases hmem : f ∈ Finset.image u Finset.univ
    · obtain ⟨x0, -, hx0⟩ := Finset.mem_image.mp hmem
      rw [if_pos hmem, Finset.sum_eq_single x0]
      · simp [isoMatrix, Matrix.conjTranspose_apply, hx0]
      · intro x _ hx
        have hne : u x ≠ f := fun h => hx (hu (h.trans hx0.symm))
        simp [isoMatrix, Matrix.conjTranspose_apply, hne]
      · intro h
        exact absurd (Finset.mem_univ x0) h
    · rw [if_neg hmem]
      refine Finset.sum_eq_zero fun x _ => ?_
      have hne : u x ≠ f := fun h => hmem (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, h⟩)
      simp [isoMatrix, Matrix.conjTranspose_apply, hne]
  · rw [if_neg hff]
    refine Finset.sum_eq_zero fun x _ => ?_
    simp only [isoMatrix, Matrix.conjTranspose_apply, RCLike.star_def]
    by_cases h1 : u x = f
    · have h2 : u x ≠ f' := fun h => hff (h1.symm.trans h)
      simp [h1, hff]
    · simp [h1]
